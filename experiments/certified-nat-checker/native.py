"""Fresh native reproduction for the preserved original-cqueens endpoint.

Called only after the selected Lean proof closure passes its exhaustive audit.
No historical objects or executables are inputs. Native execution is an external
observation, not a stock-kernel numeral proof.
"""
from pathlib import Path
import hashlib
import json
import os
import re
import resource
import shutil
import subprocess
import sys
import time

LABEL = 'ADWH.Chapter15.Queens.BitRepresentation.cqueens'


def digest(path):
    with Path(path).open('rb') as stream:
        return hashlib.file_digest(stream, 'sha256').hexdigest()


def observe(spec_path):
    """Preserve separate streams and status, including expected rejections."""
    spec_path = Path(spec_path)
    spec = json.loads(spec_path.read_text())
    stdout, stderr = spec_path.with_suffix('.stdout'), spec_path.with_suffix('.stderr')
    resource.setrlimit(resource.RLIMIT_FSIZE, (1024 * 1024, 1024 * 1024))
    started = time.monotonic()
    with stdout.open('wb') as out, stderr.open('wb') as err:
        result = subprocess.run(spec['argv'], stdout=out, stderr=err, check=False)
    record = {'argv': spec['argv'], 'exit': result.returncode,
              'wall_seconds': time.monotonic() - started,
              'peak_child_rss_kib': resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss,
              'stdout_sha256': digest(stdout), 'stderr_sha256': digest(stderr)}
    record['passed'] = (result.returncode == spec['expected_exit'] and
                        stdout.read_bytes() == spec['expected_stdout'].encode() and
                        stderr.read_bytes() == b'')
    spec_path.with_suffix('.result.json').write_text(json.dumps(record, indent=2) + '\n')
    if not record['passed']:
        raise RuntimeError(f'Native output/status mismatch: {spec_path}')


def reproduce(lean, source, output, rows, commands, started):
    here = Path(__file__).resolve().parent
    limited = [sys.executable, str(here / 'reproduce.py'), '--exec-limited']

    def run(label, argv):
        remaining = 1200 - (time.monotonic() - started)
        if remaining <= 0:
            raise RuntimeError('Total 20-minute time limit')
        argv = list(map(str, argv))
        if not Path(argv[0]).is_absolute():
            resolved = shutil.which(argv[0])
            if not resolved:
                raise RuntimeError(f'Missing native tool: {argv[0]}')
            argv[0] = resolved
        commands.run(label, limited + argv, source,
                     timeout=min(120, remaining))

    # The Nix-patched leanc wrapper can otherwise select a different compiler
    # through inherited LEAN_CC. Bind it explicitly to this development shell.
    cc = shutil.which('cc')
    if not cc:
        raise RuntimeError('Native reproduction requires cc in the pinned development shell')
    cc = Path(cc).absolute()
    leanc = lean.with_name('leanc')
    commands.env['LEAN_CC'] = str(cc)
    for key in ['LEAN_CFLAGS', 'LEAN_LDFLAGS']:
        if commands.env.get(key):
            raise RuntimeError(f'Unexpected native compiler override: {key}')
    tools = {lean, leanc, cc}
    if leanc.with_name('leanc.orig').exists():
        tools.add(leanc.with_name('leanc.orig'))
    for name in ['cc1', 'as', 'ld']:
        run('native-tool-' + name, [cc, '-print-prog-name=' + name])
        path = Path((commands.directory / ('native-tool-' + name + '.log')).read_text().strip())
        if not path.is_absolute():
            resolved = shutil.which(str(path))
            path = Path(resolved) if resolved else path
        if not path.is_absolute() or not path.is_file():
            raise RuntimeError(f'Cannot bind native tool: {name}: {path}')
        tools.add(path)
    # Include the whole shipped native header/library inventory, not olean
    # caches. This is deliberately a superset of the libraries used by leanc.
    prefix = lean.parent.parent
    tools.update(p for p in (prefix / 'include').rglob('*') if p.is_file())
    tools.update(p for p in (prefix / 'lib').rglob('*')
                 if p.is_file() and (p.name.endswith('.a') or '.so' in p.name))
    identities = {str(p): digest(p) for p in sorted(tools)}
    # Nix store closure names and NAR hashes bind the selected C compiler's
    # support files (assembler, linker, headers, libc and wrapper configuration).
    store = next((p for p in [cc, *cc.parents] if p.parent == Path('/nix/store')), None)
    if store is None:
        raise RuntimeError('Native C compiler must come from the pinned Nix shell')
    run('native-nix-closure-before', ['nix', 'path-info', '--json', '--json-format', '1', '--recursive', store])
    nix_before = json.loads((commands.directory / 'native-nix-closure-before.log').read_text())
    native = {'compiler_files': identities, 'cc': str(cc), 'leanc': str(leanc),
              'nix_compiler_closure': nix_before,
              'environment': {k: v for k, v in commands.env.items()
                              if k.startswith('NIX_') or k in ['PATH', 'LEAN_CC', 'LEAN_PATH', 'LEAN_NUM_THREADS']},
              'timing_note': 'C generation includes repeated Lean frontend checking.'}
    (output.parent / 'native-provenance.json').write_text(json.dumps(native, indent=2) + '\n')
    objects = []
    for row in rows:
        relative = Path(*row['module'].split('.'))
        c = (output / relative).with_suffix('.c')
        run('generate-' + row['module'], [lean, '-j1', '-DautoImplicit=false',
            '-DwarningAsError=true', '-DElab.async=false', '-R', source, '-c', c,
            (source / relative).with_suffix('.lean')])
    for row in rows:
        relative = Path(*row['module'].split('.'))
        c, obj = (output / relative).with_suffix('.c'), (output / relative).with_suffix('.o')
        run('compile-c-' + row['module'], [leanc, '-O3', '-Werror', '-c', c, '-o', obj])
        objects.append(obj)
    executable = output / 'first-row-reflection-original-queens-checker'
    run('native-link', [leanc, '-O3', '-Werror', *objects, '-o', executable])
    executable_hash = digest(executable)
    run('native-runtime-dependencies', ['ldd', executable])
    dependencies = (commands.directory / 'native-runtime-dependencies.log').read_text()
    runtime = {p: digest(p) for p in re.findall(r'(/[^\s()]+)', dependencies)}
    if 'not found' in dependencies:
        raise RuntimeError('Missing native runtime dependency')
    native.update(executable_sha256=executable_hash, runtime_files=runtime)
    (output.parent / 'native-provenance.json').write_text(json.dumps(native, indent=2) + '\n')
    cases = [
        ('canonical16', [LABEL, '16', '=', '14772512'], 0,
         f'ACCEPT {LABEL} 16 = 14772512\n'),
        ('canonical0', [LABEL, '0', '=', '1'], 0, f'ACCEPT {LABEL} 0 = 1\n'),
        ('wrong-value', [LABEL, '0', '=', '2'], 1, 'REJECT\n'),
        ('wrong-source', ['other.cqueens', '0', '=', '1'], 1, 'REJECT\n'),
        ('wrong-operator', [LABEL, '0', '==', '1'], 1, 'REJECT\n'),
        ('noncanonical', [LABEL, '00', '=', '1'], 1, 'REJECT\n'),
        ('extra-token', [LABEL, '0', '=', '1', 'extra'], 1, 'REJECT\n'),
    ]
    observations = {}
    for name, args, code, text in cases:
        spec = output.parent / ('native-' + name + '.json')
        spec.write_text(json.dumps({'argv': [str(executable), *args],
                                   'expected_exit': code, 'expected_stdout': text}) + '\n')
        run('execute-' + name, [sys.executable, __file__, '--observe', spec])
        observations[name] = json.loads(spec.with_suffix('.result.json').read_text())
    if digest(executable) != executable_hash:
        raise RuntimeError('Native executable changed during observation')
    if any(digest(p) != h for p, h in {**identities, **runtime}.items()):
        raise RuntimeError('Native compiler/runtime changed during reproduction')
    run('native-nix-closure-after', ['nix', 'path-info', '--json', '--json-format', '1', '--recursive', store])
    if json.loads((commands.directory / 'native-nix-closure-after.log').read_text()) != nix_before:
        raise RuntimeError('Nix compiler closure changed during reproduction')
    native['observations'] = observations
    native['timings_seconds'] = {
        stage: sum(r['wall_seconds'] for r in commands.records if r['label'].startswith(prefix))
        for stage, prefix in [('generation_with_rechecking', 'generate-'),
                              ('c_compilation', 'compile-c-'), ('link', 'native-link'),
                              ('execution_and_controls', 'execute-')]}
    (output.parent / 'native-provenance.json').write_text(json.dumps(native, indent=2) + '\n')
    return native


if __name__ == '__main__':
    if len(sys.argv) != 3 or sys.argv[1] != '--observe':
        raise SystemExit('Called by reproduce.py; expected --observe SPEC.json')
    observe(sys.argv[2])
