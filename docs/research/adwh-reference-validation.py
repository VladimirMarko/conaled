"""Revalidate ADWH checkpoint 233 in a new directory; run through direnv.
Usage: python3 docs/research/adwh-reference-validation.py NEW_STATE_DIRECTORY
"""
from datetime import datetime, timezone
from pathlib import Path
import concurrent.futures as cf, hashlib, importlib.util, json, os, re, subprocess, time, traceback, sys, zipfile, shutil
S = Path(sys.argv[1]).resolve()
S.mkdir(exist_ok=False, parents=True)

def save(n, v):
    (S / n).write_text(json.dumps(v, indent=2) + '\n')

def stop():
    if any(((S.parent / n).exists() for n in ['STOP', 'USAGE-UNKNOWN'])):
        raise RuntimeError('Coordinator stop sentinel')
start = time.monotonic()
result = {'status': 'running', 'stage': 'integrity', 'started_utc': datetime.now(timezone.utc).isoformat()}
save('result.json', result)
try:
    stop()
    archive_root = Path(__file__).resolve().parents[1] / 'history/algorithm-design-haskell'
    meta = json.loads((archive_root / 'checkpoint-233.json').read_text())

    def sha(p):
        with p.open('rb') as f:
            return hashlib.file_digest(f, 'sha256').hexdigest()
    result['stage'] = 'archive_integrity'
    assert sha(archive_root / meta['archive']) == meta['archive_sha256']
    assert sha(archive_root / meta['member_manifest']) == meta['member_manifest_sha256']
    result['stage'] = 'archive_restoration'
    restored = S / 'restored'
    with zipfile.ZipFile(archive_root / meta['archive']) as z:
        z.extractall(restored)
    result['stage'] = 'member_integrity'
    rows = (archive_root / meta['member_manifest']).read_text().splitlines()
    assert len(rows) == meta['regular_files']
    for row in rows:
        h, n = row.split('  ', 1)
        assert sha(restored / n) == h, n
    result['stage'] = 'prepare_sources'
    B = S / 'build'
    shutil.copytree(restored / 'project/adwh-lean', B)
    O = S / 'fresh-objects'
    O.mkdir(exist_ok=False)
    spec = importlib.util.spec_from_file_location('gate', B / 'scripts/check.py')
    g = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(g)
    stop()
    result['stage'] = 'source_gate'
    before = g.source_gate(B, 'ADWH')
    controls = g.control_gate()
    supplied = json.loads((B / 'reports/verification.json').read_text())
    assert before == supplied['files']
    assert controls == supplied['verification_controls']
    assert len(before) == 1240
    assert not list(B.rglob('*.olean'))
    save('source-and-controls.json', {'files': before, 'verification_controls': controls})
    lean = subprocess.check_output(['elan', 'which', 'lean'], text=True).strip()
    version = subprocess.check_output([lean, '--version'], text=True).strip()
    assert version == supplied['lean_version']
    result['lean_version'] = version
    env = dict(os.environ, LEAN_PATH=str(O))
    sources = {f['module']: B / f['path'] for f in before}
    deps = {}
    for name, p in sources.items():
        imports = re.findall('^\\s*import[ \\t]+([^\\n]+)$', g.lean_code(p.read_text()), re.M)
        deps[name] = {i for line in imports for i in line.split() if i in sources}
    commands = []
    done = set()
    pending = set(sources)
    active = {}
    (S / 'modules').mkdir()
    buildstart = time.monotonic()
    result['stage'] = 'fresh_build'

    def compile(name):
        out = O / (name.replace('.', '/') + '.olean')
        out.parent.mkdir(parents=True, exist_ok=True)
        cmd = [lean, '-j1', '-DautoImplicit=false', '-DwarningAsError=true', '-o', str(out), str(sources[name].relative_to(B))]
        t = time.monotonic()
        with (S / 'modules' / f'{name}.log').open('w') as log:
            p = subprocess.run(cmd, cwd=B, env=env, stdout=log, stderr=subprocess.STDOUT)
        return {'module': name, 'command': cmd, 'cwd': str(B), 'LEAN_PATH': str(O), 'returncode': p.returncode, 'seconds': time.monotonic() - t}
    with cf.ThreadPoolExecutor(max_workers=4) as pool:
        while pending or active:
            stop()
            ready = sorted((n for n in pending if deps[n] <= done))
            for n in ready[:4 - len(active)]:
                pending.remove(n)
                active[pool.submit(compile, n)] = n
            assert active, 'Dependency cycle'
            completed, _ = cf.wait(active, timeout=2, return_when=cf.FIRST_COMPLETED)
            for f in completed:
                n = active.pop(f)
                record = f.result()
                commands.append(record)
                with (S / 'commands.jsonl').open('a') as log:
                    log.write(json.dumps(record) + '\n')
                if record['returncode']:
                    raise RuntimeError(f'Compilation failed: {n}; see modules log')
                done.add(n)
            save('progress.json', {'completed': len(done), 'total': len(sources), 'active': list(active.values()), 'seconds': time.monotonic() - buildstart})
    result['compiled_modules'] = len(done)
    result['build_seconds'] = time.monotonic() - buildstart
    result['stage'] = 'audit'
    save('result.json', result)
    stop()
    cmd = [lean, '-j1', '-DautoImplicit=false', '-DwarningAsError=true', 'scripts/Audit.lean']
    t = time.monotonic()
    with (S / 'proof-audit.jsonl').open('w') as log:
        p = subprocess.run(cmd, cwd=B, env=env, stdout=log, stderr=subprocess.STDOUT)
    save('audit-command.json', {'command': cmd, 'cwd': str(B), 'LEAN_PATH': str(O), 'returncode': p.returncode})
    assert p.returncode == 0
    records = [json.loads(l) for l in (S / 'proof-audit.jsonl').read_text().splitlines() if l.strip()]
    summary = records.pop()
    assert summary['status'] == 'passed' and summary['declarations'] == len(records)
    assert len({r['declaration'] for r in records}) == len(records)
    assert all((set(r['axioms']) <= set(g.ALLOWED_AXIOMS) for r in records))
    result['audit'] = summary
    result['audit_seconds'] = time.monotonic() - t
    result['stage'] = 'coverage'
    stop()
    coverage = g.validate_coverage(B / 'reports/coverage.json', records, [], False)
    save('coverage-validation.json', coverage)
    assert coverage['status'] == 'passed'
    result['coverage'] = {k: v for k, v in coverage.items() if not isinstance(v, list)}
    assert before == g.source_gate(B, 'ADWH') and controls == g.control_gate()
    result['source_and_controls_unchanged'] = True
    result['status'] = 'passed'
    result['stage'] = 'completed'
except BaseException as e:
    result['status'] = 'failed'
    result['error'] = str(e)
    (S / 'failure.log').write_text(traceback.format_exc())
    raise
finally:
    result['total_seconds'] = time.monotonic() - start
    save('result.json', result)
