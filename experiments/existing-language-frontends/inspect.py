#!/usr/bin/env python3
"""Run diagnostic compiler probes, not a conaled importer or proof checker.

Use a new private work directory. Full commands/output and generated artifacts
remain there. The caller separately retains source/toolchain provenance.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    for name in ('agda', 'agda-data', 'stdlib', 'ghc', 'work'):
        ap.add_argument('--' + name, type=Path, required=True)
    args = ap.parse_args()
    root = Path(__file__).resolve().parent
    work = args.work.resolve()
    work.mkdir()  # Never overwrite an earlier run.
    clients = work / 'clients'
    shutil.copytree(root / 'clients', clients)
    stdlib = work / 'stdlib'
    shutil.copytree(args.stdlib, stdlib, ignore=shutil.ignore_patterns('*.agdai', '_build', '.git'))
    data = work / 'agda-data'
    shutil.copytree(args.agda_data, data, ignore=shutil.ignore_patterns('*.agdai'))
    (work / 'config').mkdir()
    env = os.environ.copy()
    env.update(Agda_datadir=str(data), AGDA_DIR=str(work / 'config'))
    env['PATH'] = str(args.ghc.resolve().parent) + os.pathsep + env['PATH']
    commands = []
    artifacts = []

    def run(name, argv, expected=0, timeout=120):
        p = subprocess.run([str(a) for a in argv], cwd=work, env=env,
                           text=True, capture_output=True, timeout=timeout)
        output = p.stdout + p.stderr
        (work / (name + '.log')).write_text(output)
        commands.append({'name': name, 'argv': list(map(str, argv)),
                         'exit': p.returncode, 'log_sha256': sha(work / (name + '.log'))})
        (work / 'commands.json').write_text(json.dumps(commands, indent=2) + '\n')
        if expected is not None and p.returncode != expected:
            raise RuntimeError(f'{name}: expected exit {expected}, got {p.returncode}; see log')
        return output, p.returncode

    ghc = args.ghc.resolve()
    agda = args.agda.resolve()
    ghc_version = run('ghc-version', [ghc, '--numeric-version'])[0].strip()
    agda_version = run('agda-version', [agda, '--version'])[0].strip()
    if ghc_version != '9.10.3' or agda_version.splitlines()[0] != 'Agda version 2.8.0.2':
        raise RuntimeError('This diagnostic corpus is pinned to GHC 9.10.3 and Agda 2.8.0.2')
    if sha(agda) != '3fe070780fa370f5b74e5716ebe42fb60ec6b0ad90d13f8ab45d2903abf39b84':
        raise RuntimeError('Agda executable differs from the retained official binary')
    ghcpkg = ghc.parent / 'ghc-pkg'
    packages = run('packages', [ghcpkg, 'list', '--simple-output'])[0].strip()
    imports = run('ghc-internal-location', [ghcpkg, 'field', 'ghc-internal', 'import-dirs', '--simple-output'])[0].strip()
    iface = Path(imports) / 'GHC/Internal/Data/Either.hi'
    interface = run('either-interface', [ghc, '--show-iface', iface])[0]
    artifacts.append(('GHC installed Either interface', interface))
    hs = clients / 'HaskellClient.hs'
    for optimization in ('0', '1'):
        out = work / ('ghc-O' + optimization)
        out.mkdir()
        core = run('core-O' + optimization, [ghc, '-O' + optimization, '-fforce-recomp',
                   '-c', hs, '-outputdir', out, '-ddump-ds', '-ddump-simpl',
                   '-dcore-lint', '-dsuppress-uniques'])[0]
        artifacts.append(('GHC desugared and simplified Core O' + optimization, core))
    expected = [False, True, True, False, True, False, True, False,
                False, False, True, True, False, True, True, False, True, False]

    def parse_bools(output):
        # GHC print gives a single list, never execute output as Python code.
        text = output.strip()
        if not re.fullmatch(r'\[(?:True|False)(?:,(?:True|False))*\]', text):
            raise RuntimeError('Unexpected Boolean observation format: ' + text)
        return [x == 'True' for x in text[1:-1].split(',')]

    hsout = run('haskell-observations', [ghc, '-ignore-dot-ghci', hs, '-e', 'print observations'])[0]
    if parse_bools(hsout) != expected:
        raise RuntimeError('Haskell observations differ from independent Boolean oracle')
    lazy = run('haskell-unused-bottom', [ghc, '-ignore-dot-ghci', hs, '-e', 'print unusedBottom'])[0]
    if lazy.strip() != 'True':
        raise RuntimeError('Unused branch observation changed')
    bottom, bottom_exit = run('haskell-forced-bottom', [ghc, '-ignore-dot-ghci', hs, '-e', 'print forcedBottom'], expected=None)
    if bottom_exit == 0 or 'undefined' not in bottom:
        raise RuntimeError('Forced-bottom control did not fail as expected')
    agda_flags = [agda, '--no-libraries', '-i', clients, '-i', stdlib / 'src']
    run('agda-check', agda_flags + [clients / 'AgdaClient.agda'])
    inspector = root.parent / 'agda-internal-retention/inspect_interface.py'
    for label, search_root, ending, names in [
        ('agda-internal-client', clients, 'AgdaClient.agdai',
         ['AgdaClient.choose', 'AgdaClient.step', 'AgdaClient.observations-correct']),
        ('agda-internal-sum', stdlib, 'Data/Sum/Base.agdai', ['Data.Sum.Base.[_,_]′'])]:
        matches = [p for p in search_root.rglob('*.agdai') if str(p).endswith(ending)]
        if len(matches) != 1:
            raise RuntimeError('Missing or ambiguous fresh interface: ' + ending)
        dump = run(label, [sys.executable, inspector, matches[0], *names])[0]
        artifacts.append((label + ' (bounded #115 decoder, not independent typechecking)', dump))
    generated = work / 'generated'
    run('agda-haskell', agda_flags + ['--compile', '--ghc-dont-call-ghc', '--no-main',
        '--compile-dir=' + str(generated), clients / 'AgdaClient.agda'])
    generated_client = generated / 'MAlonzo/Code/AgdaClient.hs'
    source = generated_client.read_text()
    artifacts.append(('Agda generated client', source))
    artifacts.append(('Agda generated standard library sum',
                      (generated / 'MAlonzo/Code/Data/Sum/Base.hs').read_text()))
    match = re.search(r'^(d_observations_\d+)\s*::', source, re.M)
    if not match:
        raise RuntimeError('No uniquely named generated observations binding')
    agdaout = run('agda-observations', [ghc, '-ignore-dot-ghci', '-i' + str(generated),
               generated_client, '-e', 'print ' + match.group(1)])[0]
    if parse_bools(agdaout) != expected:
        raise RuntimeError('Agda generated execution differs from independent Boolean oracle')
    bad = clients / 'Unsafe.agda'
    bad.write_text('{-# OPTIONS --safe #-}\nmodule Unsafe where\nopen import Agda.Builtin.Bool\npostulate fabricated : Bool\n')
    diagnostic, code = run('agda-safe-postulate', agda_flags + [bad], expected=None)
    if code == 0 or 'postulate' not in diagnostic.lower():
        raise RuntimeError('Safe-postulate control did not reject')
    artifacts.append(('Executed Agda rejection', diagnostic))
    artifacts.append(('Executed Haskell forcing discriminator', bottom))
    manifest = {'ghc_version': ghc_version, 'ghc_binary_sha256': sha(ghc),
                'ghc_path': str(ghc), 'agda_version': agda_version,
                'agda_binary_sha256': sha(agda), 'packages': packages,
                'either_interface_sha256': sha(iface),
                'clients': {p.name: sha(p) for p in (root / 'clients').iterdir()},
                'stdlib_source_count': len(list(stdlib.rglob('*.agda'))),
                'stdlib_source_tree_sha256': hashlib.sha256(json.dumps(
                    {str(p.relative_to(stdlib)): sha(p) for p in sorted(stdlib.rglob('*.agda'))},
                    sort_keys=True, separators=(',', ':')).encode()).hexdigest(),
                'inspector_sha256': sha(inspector),
                'generated_files': {str(p.relative_to(generated)): sha(p) for p in sorted(generated.rglob('*.hs'))},
                'commands': commands}
    (work / 'manifest.json').write_text(json.dumps(manifest, indent=2) + '\n')
    results = {'status': 'diagnostic checks passed', 'expected': expected,
               'haskell': parse_bools(hsout), 'agda_generated_haskell': parse_bools(agdaout),
               'unused_bottom': True, 'forced_bottom_exit': bottom_exit,
               'safe_postulate_exit': code, 'conaled_import_performed': False,
               'treeless_dump_obtained': False, 'full_proof_transport_established': False}
    (work / 'results.json').write_text(json.dumps(results, indent=2) + '\n')
    (work / 'artifacts.txt').write_text('\n\n'.join('=== ' + name + ' ===\n' + text for name, text in artifacts))
    print(json.dumps(results))


if __name__ == '__main__':
    main()
