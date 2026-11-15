#!/usr/bin/env python3
"""Verify frozen evidence and replay both arms against the same oracle."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import tempfile
import tarfile

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[3]
COHORT = HERE.parent

def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def check():
    freeze = json.loads((COHORT / 'freeze.json').read_text())
    manifest = json.loads((HERE / 'authors/manifest.json').read_text())
    for name, expected in freeze['source_sha256'].items():
        assert digest(REPO / name) == expected, name
    for arm, files in manifest['files'].items():
        for name, expected in files.items():
            assert digest(HERE / 'authors' / arm / name) == expected, (arm, name)
    for name, expected in freeze['public_sha256'].items():
        # The freeze manifest uses public-relative keys.
        path = COHORT / name if name.startswith('public/') else COHORT / 'public' / name
        assert digest(path) == expected, name
    assert digest(HERE / 'preparation-private-archive.tar.gz') == freeze['private_archive']['sha256']
    with tarfile.open(HERE / 'preparation-private-archive.tar.gz') as archive:
        members = {m.name: m for m in archive.getmembers() if m.isfile()}
        assert set(members) == set(freeze['private_archive']['file_sha256'])
        for name, expected in freeze['private_archive']['file_sha256'].items():
            assert hashlib.sha256(archive.extractfile(members[name]).read()).hexdigest() == expected, name
    for name, expected in freeze['private_artifact_sha256'].items():
        if name.startswith('checkout/'):
            assert digest(HERE / 'preparation' / Path(name).name) == expected, name
    oracle = (HERE / 'preparation/PrivateOracle.lean').read_text()
    body = oracle.split('\n', 1)[1]
    # Frozen body identity omits the final newline; replay itself retains it.
    assert hashlib.sha256(body.rstrip('\n').encode()).hexdigest() == freeze['oracle_body_sha256']
    assert body == (HERE / 'preparation/PrivateOracleFacade.lean').read_text().split('\n', 1)[1]
    module = REPO / 'Examples/UnivalentAuthorTrial'
    task = (COHORT / 'public/TrialTask.lean').read_bytes()
    assert (module / 'Task.lean').read_bytes() == task
    for arm in ('direct', 'facade'):
        cap = arm.title()
        source = (HERE / 'authors' / arm / 'AuthorSubmission.lean').read_text()
        adapted = source.replace('import TrialTask', 'import Examples.UnivalentAuthorTrial.Task').replace('JournalTrial.Author', f'JournalTrial.{cap}Author')
        assert (module / f'{cap}.lean').read_text() == adapted
        adapted_oracle = ('import Examples.UnivalentAuthorTrial.' + cap + '\n' + body).replace('JournalTrial.Oracle', f'JournalTrial.{cap}Oracle').replace('Author.', f'{cap}Author.')
        assert (module / f'{cap}Oracle.lean').read_text() == adapted_oracle
    print('PASS: frozen author evidence, public task, preparation archive, identical oracle bodies and integrated adaptation identities')
    return body

def replay(output, body):
    output.mkdir(parents=True, exist_ok=False)
    lean_path = subprocess.check_output(['lake', 'env', 'printenv', 'LEAN_PATH'], cwd=REPO, text=True).strip()
    # Lake paths may be relative to the repository, while scratch modules are not.
    lean_path = os.pathsep.join(str((REPO / p).resolve()) if not Path(p).is_absolute() else p for p in lean_path.split(os.pathsep))
    records = {}
    for arm in ('direct', 'facade', 'preparation'):
        folder = output / arm
        folder.mkdir()
        shutil.copy2(REPO / 'lean-toolchain', folder / 'lean-toolchain')
        shutil.copy2(COHORT / 'public/TrialTask.lean', folder / 'TrialTask.lean')
        if arm == 'preparation':
            for path in (HERE / 'preparation').glob('*.lean'):
                shutil.copy2(path, folder / path.name)
            modules = ['TrialTask', 'PrivateMathematics', 'PrivateFeasibility', 'PrivateOracle', 'PrivateFacadeFeasibility', 'PrivateOracleFacade', 'InterfaceNative', 'InterfaceFacade']
        else:
            shutil.copy2(HERE / 'authors' / arm / 'AuthorSubmission.lean', folder / 'AuthorSubmission.lean')
            shutil.copy2(COHORT / 'public/ExpectedInterface.lean', folder / 'ExpectedInterface.lean')
            (folder / 'PrivateOracle.lean').write_text('import AuthorSubmission\n' + body)
            modules = ['TrialTask', 'AuthorSubmission', 'ExpectedInterface', 'PrivateOracle']
        env = dict(os.environ, LEAN_PATH=lean_path + os.pathsep + str(folder))
        log = folder / 'replay.log'
        with log.open('w') as stream:
            for module in modules:
                command = ['lean', '-o', module + '.olean', module + '.lean']
                stream.write('COMMAND ' + ' '.join(command) + '\n'); stream.flush()
                result = subprocess.run(command, cwd=folder, env=env, stdout=stream, stderr=subprocess.STDOUT)
                stream.write(f'EXIT {result.returncode}\n'); stream.flush()
                if result.returncode:
                    raise SystemExit(f'Failed {arm}/{module}; see {log}')
        records[arm] = {'status': 'PASS', 'log_sha256': digest(log)}
    (output / 'replay.json').write_text(json.dumps(records, indent=2) + '\n')
    print('PASS: both unchanged submissions and both private feasibility solutions; logs:', output)

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--run', action='store_true', help='also replay Lean under the shared thermal lock')
    parser.add_argument('--output', type=Path, help='new directory for replay modules and logs')
    parser.add_argument('--environment', type=Path, default=REPO, help='authorized direnv checkout with the same pinned environment')
    parser.add_argument('--locked', action='store_true', help=argparse.SUPPRESS)
    args = parser.parse_args()
    body = check()
    if args.locked:
        replay(args.output.resolve(), body)
    elif args.run:
        for name in ('flake.nix', 'flake.lock', 'lean-toolchain', 'lake-manifest.json'):
            assert digest(args.environment / name) == digest(REPO / name), name
        output = args.output.resolve() if args.output else Path(tempfile.mkdtemp(prefix='conaled-534-parent-')) / 'replay'
        Path('/tmp/conaled-wave-20261115').mkdir(exist_ok=True)
        command = ['flock', '/tmp/conaled-wave-20261115/build.lock', 'taskset', '-c', '0', 'nice', '-n', '10', 'direnv', 'exec', str(args.environment.resolve()), 'python3', str(Path(__file__).resolve()), '--locked', '--output', str(output)]
        subprocess.run(command, cwd=REPO, check=True)

if __name__ == '__main__':
    main()
