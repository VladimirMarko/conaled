#!/usr/bin/env python3
"""Optional Codex CLI warning; never blocks a turn or supplies model context."""
import argparse
import contextlib
import datetime as dt
import fcntl
import hashlib
import json
import os
from pathlib import Path
import shlex
import sys
import tempfile

ROOT = Path(__file__).resolve().parent.parent
POLICY = ROOT / '.agents/model-policy.json'
TAIL_BYTES = 4 * 1024 * 1024


def read_json(path):
    return json.loads(Path(path).read_text())


def write_json(path, value):
    path = Path(path)
    path.parent.mkdir(parents=True, exist_ok=True)
    fd, temporary = tempfile.mkstemp(dir=path.parent, prefix='.' + path.name)
    try:
        with os.fdopen(fd, 'w') as stream:
            json.dump(value, stream, indent=2)
            stream.write('\n')
        os.replace(temporary, path)
    finally:
        if os.path.exists(temporary):
            os.unlink(temporary)


def current_effort(event):
    """Only a complete, matching turn_context may supply the current effort."""
    turn, model = event.get('turn_id'), event.get('model')
    if not isinstance(turn, str) or not turn or not isinstance(model, str) or not model:
        return None, 'missing current turn or model'
    transcript = event.get('transcript_path')
    if not transcript:
        return None, 'no transcript path'
    try:
        with open(transcript, 'rb') as stream:
            header = json.loads(stream.readline())
            if (header.get('type') != 'session_meta'
                    or header.get('payload', {}).get('id') != event.get('session_id')):
                return None, 'transcript belongs to another session or has no session identity'
            stream.seek(0, os.SEEK_END)
            size = stream.tell()
            stream.seek(max(0, size - TAIL_BYTES))
            if size > TAIL_BYTES:
                stream.readline()  # The window may start in a JSON record.
            lines = stream.read().splitlines(keepends=True)
        for line in reversed(lines):
            if not line.endswith(b'\n'):
                continue
            try:
                record = json.loads(line)
            except (ValueError, UnicodeError):
                continue
            if not isinstance(record, dict) or record.get('type') != 'turn_context':
                continue
            context = record.get('payload', {})
            if not isinstance(context, dict) or context.get('turn_id') != turn:
                continue
            if context.get('model') != model:
                return None, 'current turn model differs from hook model'
            effort = context.get('effort')
            if isinstance(effort, str) and effort:
                return effort, 'matching transcript turn_context'
            return None, 'current turn effort unavailable'
    except (OSError, ValueError):
        return None, 'transcript unavailable'
    return None, 'current turn_context not found in transcript tail'


def evaluate(event, policy, exceptions=None, now=None):
    if policy.get('version') != 1 or not isinstance(policy.get('approved'), list):
        raise ValueError('unsupported model policy')
    effort, evidence = current_effort(event)
    model = event.get('model')
    result = {key: event.get(key) for key in ('session_id', 'agent_id', 'turn_id', 'model')}
    result.update(effort=effort, evidence=evidence)
    if not event.get('session_id') or not event.get('turn_id') or not isinstance(model, str) or not effort:
        status = 'unknown'
    elif any(item['model'] == model and effort in item['efforts'] for item in policy['approved']):
        status = 'approved'
    else:
        status = 'unapproved'
    now = now or dt.datetime.now(dt.timezone.utc)
    for exception in (exceptions or {}).get('exceptions', []):
        # Exact session, agent, model and effort; null effort explicitly covers unknown.
        expiry = dt.datetime.fromisoformat(exception['expires_at'].replace('Z', '+00:00'))
        if (expiry.tzinfo is not None and expiry > now and exception.get('reason')
                and event.get('session_id') and event.get('turn_id')
                and all(exception.get(key) == result.get(key)
                        for key in ('session_id', 'agent_id', 'model', 'effort'))):
            status = 'exception'
            result['exception_reason'] = exception['reason']
            break
    result['status'] = status
    return result


def warning(result):
    status = result['status']
    configuration = f"{result.get('model') or 'unknown model'} / {result.get('effort') or 'unknown effort'}"
    if status == 'unapproved':
        return f'🟥 Model warning: {configuration} is outside the configured defaults. Check the selection or record a scoped exception; work continues.'
    if status == 'unknown':
        return f'⚠ Model warning: cannot determine current configuration ({configuration}; {result["evidence"]}). Work continues.'
    if status == 'exception':
        return f'Model exception: {configuration}.'
    return f'Model: {configuration}'


def observe(event, policy, state_dir, exceptions=None):
    result = evaluate(event, policy, exceptions)
    identity = [event.get('cwd'), event.get('session_id'), event.get('agent_id')]
    key = hashlib.sha256(json.dumps(identity).encode()).hexdigest()
    state_dir = Path(state_dir)
    state_dir.mkdir(parents=True, exist_ok=True)
    path = state_dir / (key + '.json')
    with (state_dir / (key + '.lock')).open('a') as lock:
        fcntl.flock(lock, fcntl.LOCK_EX)
        previous = read_json(path) if path.exists() else None
        signature = lambda r: [r.get(k) for k in ('status', 'model', 'effort', 'evidence', 'exception_reason')]
        changed = previous is None or signature(previous) != signature(result)
        result['observed_at'] = dt.datetime.now(dt.timezone.utc).isoformat()
        write_json(path, result)
    # Approved configurations stay quiet; report recovery from another status once.
    emit = changed and (result['status'] != 'approved'
                        or (previous is not None and previous['status'] != 'approved'))
    return result, {'systemMessage': warning(result)} if emit else {}


def install(args):
    target = Path(args.hooks_file).expanduser().resolve()
    if args.write:
        target.parent.mkdir(parents=True, exist_ok=True)
    lock_file = target.parent / (target.name + '.lock')
    with lock_file.open('a') if args.write else contextlib.nullcontext() as lock:
        if lock is not None:
            fcntl.flock(lock, fcntl.LOCK_EX)
        config = read_json(target) if target.exists() else {}
        command = shlex.join([sys.executable, str(Path(__file__).resolve()), 'hook', '--policy', str(Path(args.policy).resolve()), '--state-dir', str(Path(args.state_dir).expanduser().resolve())])
        if args.exceptions:
            command += ' --exceptions ' + shlex.quote(str(Path(args.exceptions).expanduser().resolve()))
        handler = {'type': 'command', 'command': command, 'timeout': 5}
        entries = config.setdefault('hooks', {}).setdefault('UserPromptSubmit', [])
        if not any(handler == h for entry in entries for h in entry.get('hooks', [])):
            entries.append({'hooks': [handler]})
        if args.write:
            write_json(target, config)
        print(json.dumps(config, indent=2))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('action', choices=['hook', 'inspect', 'install'])
    parser.add_argument('--policy', default=str(POLICY))
    parser.add_argument('--state-dir', default=str(Path(os.environ.get('XDG_CACHE_HOME', Path.home() / '.cache')) / 'conaled/model-warning'))
    parser.add_argument('--exceptions', help='optional local scoped exception JSON')
    parser.add_argument('--hooks-file', default=str(ROOT / '.codex/hooks.json'))
    parser.add_argument('--write', action='store_true', help='install merged hook config; default prints proposed config')
    args = parser.parse_args()
    if args.action == 'install':
        install(args)
        return
    try:
        event = json.load(sys.stdin)
        policy = read_json(args.policy)
        exceptions = read_json(args.exceptions) if args.exceptions else None
        if args.action == 'inspect':
            print(json.dumps(evaluate(event, policy, exceptions), indent=2))
        else:
            if event.get('hook_event_name') != 'UserPromptSubmit':
                return
            _, output = observe(event, policy, args.state_dir, exceptions)
            print(json.dumps(output))
    except (OSError, ValueError, TypeError, KeyError, AttributeError) as error:
        if args.action == 'inspect':
            raise SystemExit(f'model-warning: {error}')
        # This is an advisory monitor, never an approval gate.
        print(json.dumps({'systemMessage': f'⚠ Model warning monitor unavailable: {type(error).__name__}. Work continues.'}))


if __name__ == '__main__':
    main()
