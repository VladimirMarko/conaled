#!/usr/bin/env python3
"""Exercise a checkpoint script in a disposable independent repository.

Usage: python3 checkpoint-fixture.py /absolute/path/checkpoint.py SCENARIO
Scenarios: dirty, race, selection, credential, symlink.
The source script and live project checkout are never modified. Output is JSON
plus the tested script's restoration diagnostics. No archive is uploaded.
"""
from pathlib import Path
import contextlib
import hashlib
import importlib.util
import io
import json
import shutil
import subprocess
import sys
import tarfile
import tempfile

script = Path(sys.argv[1]).resolve()
scenario = sys.argv[2]
if scenario not in ('dirty', 'race', 'selection', 'credential', 'symlink'):
    raise SystemExit('Unknown scenario')
source = script.read_bytes()
root = script.parent.parent

with tempfile.TemporaryDirectory(prefix='checkpoint-fixture-', dir=root) as td:
    fixture = Path(td)
    repo = fixture / 'conaled'
    repo.mkdir()
    session = fixture / 'session'
    session.mkdir()
    (session / 'tracker').mkdir()
    (session / 'checkpoint.py').write_bytes(source)

    def git(*args):
        return subprocess.check_output(['git', *args], cwd=repo,
                                       stderr=subprocess.STDOUT)

    git('init', '-b', 'pfds/local')
    git('config', 'user.name', 'Checkpoint fixture')
    git('config', 'user.email', 'checkpoint-fixture@example.invalid')
    (repo / '.gitignore').write_text('*.log\n')
    (repo / 'data.txt').write_text('base\n')
    (repo / 'binary.dat').write_bytes(b'\0base\xff')
    (repo / 'deleted.txt').write_text('delete me\n')
    git('add', '.')
    git('commit', '-m', 'test: baseline')
    tree = git('rev-parse', 'HEAD^{tree}').decode().strip()
    head = git('rev-parse', 'HEAD').decode().strip()
    candidate = git('commit-tree', tree, '-p', head, '-m',
                    'test: otherwise unreachable review candidate').decode().strip()
    git('update-ref', 'refs/reviews/candidate', candidate)
    git('symbolic-ref', 'refs/reviews/current', 'refs/reviews/candidate')
    git('update-ref', 'refs/remotes/origin/upstream-task', candidate)
    git('tag', '-a', 'fixture-tag', '-m', 'annotated fixture tag')
    (repo / 'data.txt').write_text('staged\n')
    (repo / 'binary.dat').write_bytes(b'\0staged\x90')
    git('add', 'data.txt', 'binary.dat')
    (repo / 'data.txt').write_text('unstaged\n')
    (repo / 'deleted.txt').unlink()
    (repo / 'untracked.txt').write_text('new source\n')
    (repo / 'untracked.bin').write_bytes(b'\0new\x80')
    status = session / 'STATUS.md'
    tickets = session / 'tracker/tickets.json'
    status.write_text('epoch 0\n')
    tickets.write_text('{"epoch":0}\n')
    if scenario == 'selection':
        (repo / 'ignored-proof.log').write_text('validation evidence marker\n')
        (session / 'scratch-proof.lean').write_text('-- proof work marker\n')
        (session / 'checkpoint-includes.json').write_text(
            '{"repo_ignored":["ignored-proof.log"]}\n')
    if scenario == 'credential':
        (session / 'auth.json').write_text(
            '{"token":"FAKE_TEST_MARKER_NOT_A_SECRET"}\n')
    if scenario == 'symlink':
        (session / 'alias.md').symlink_to(status)

    spec = importlib.util.spec_from_file_location('fixture_checkpoint',
                                                 session / 'checkpoint.py')
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    original_copy2 = shutil.copy2
    copied_status = False

    def copy_with_writer(src, dest, *args, **kwargs):
        global copied_status
        out = original_copy2(src, dest, *args, **kwargs)
        if scenario == 'race' and Path(src) == status and not copied_status:
            copied_status = True
            status.write_text('epoch 1\n')
            tickets.write_text('{"epoch":1}\n')
        return out

    stdout = io.StringIO()
    old_argv = sys.argv
    result = {'script_sha256': hashlib.sha256(source).hexdigest(),
              'scenario': scenario}
    try:
        shutil.copy2 = copy_with_writer
        sys.argv = ['checkpoint.py', '999']
        with contextlib.redirect_stdout(stdout):
            module.main()
        result['capture_exit'] = 0
    except SystemExit as error:
        result['capture_exit'] = str(error.code)
    finally:
        shutil.copy2 = original_copy2
        sys.argv = old_argv
    result['stdout'] = stdout.getvalue().strip()
    artifact = fixture / 'checkpoints/conaled-pfds-checkpoint-999.tar.gz'
    result['archive_created'] = artifact.exists()
    if artifact.exists():
        with tarfile.open(artifact) as tf:
            names = tf.getnames()
            result['captured_status'] = tf.extractfile(
                'session/STATUS.md').read().decode().strip()
            result['captured_tickets'] = json.load(tf.extractfile(
                'session/tracker/tickets.json'))
            result['scratch_lean_included'] = 'session/scratch-proof.lean' in names
            result['fake_auth_json_included'] = 'session/auth.json' in names
            manifest = json.load(tf.extractfile('manifest.json'))
            result['refs'] = manifest.get('refs', {})
            result['included_ignored_files'] = manifest.get('included_ignored_files', [])
            with tarfile.open(fileobj=tf.extractfile('untracked.tar.gz')) as ut:
                result['untracked_archive_files'] = ut.getnames()
    print(json.dumps(result, indent=2))
