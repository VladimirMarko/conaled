#!/usr/bin/env python3
"""Finite trusted registry, typed Lean obligations and immutable check records."""
import argparse
import datetime as dt
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
DEFAULT = ROOT / 'experiments/interpretation-assistance/registry.json'


class BudgetExhausted(Exception):
    pass


class CheckerFailure(Exception):
    pass


def digest(data):
    return hashlib.sha256(data).hexdigest()


def now():
    return dt.datetime.now(dt.timezone.utc).isoformat()


def render(entry):
    """Only these named route schemas are supported. Registry terms are trusted."""
    schema = entry['schema']
    d = entry['data']
    imports = ['SquareKit.InterpretationDiagnostics'] + entry['imports']
    header = '\n'.join('import ' + x for x in dict.fromkeys(imports)) + '\n\nnamespace Requested\n'
    if schema == 'extension':
        declarations = f"def selectedSource := {d['selected']}\ndef route := {d['map']}\n"
        requirements = [('extension', 'SquareKit.DiagonalConstruction.Map.Extension route selectedSource')]
        result = ('def result := route.selectedExtension selectedSource certificate_0\n'
                  'theorem observation : result.witness = route.value selectedSource.witness :=\n'
                  '  route.extension_witness selectedSource certificate_0\n')
        retained = ['result.code', 'result.witness']
    elif schema == 'image':
        declarations = f"def selectedSource := {d['selected']}\ndef route := {d['map']}\n"
        requirements = []
        result = 'def result := route.selectedImage selectedSource\n'
        retained = ['result.code', 'result.witness']
    elif schema == 'erasure':
        declarations = ''
        requirements = [('recover', 'Function.Injective (fun s : SquareKit.DiagonalConstruction.Selected '
                         '(fun _ _ : Bool => ()) id => s.witness)')]
        result = 'theorem result : requirement_0 := certificate_0\n'
        retained = ['Examples.DiagonalConstruction.erased false', 'Examples.DiagonalConstruction.erased true']
    elif schema == 'resource':
        declarations = (f"def weight : ({d['sourceCost']}) → ({d['targetCost']}) := {d['map']}\n"
                        f"def initial : Resources.Measured ({d['state']}) ({d['sourceCost']}) := {d['seed']}\n"
                        f"def transition : ({d['input']}) → ({d['state']}) → Resources.Measured ({d['state']}) ({d['sourceCost']}) := {d['step']}\n")
        requirements = [('zero', 'weight 0 = 0'),
                        ('add', f"∀ a b : ({d['sourceCost']}), weight (a+b) = weight a + weight b")]
        result = (f"def hom : ({d['sourceCost']}) →+ ({d['targetCost']}) :=\n"
                  "  { toFun := weight, map_zero' := certificate_0, map_add' := certificate_1 }\n"
                  f"theorem result (xs : List ({d['input']})) :\n"
                  '    Resources.reweight hom (Resources.bind initial (Resources.run transition xs)) =\n'
                  '    Resources.bind (Resources.reweight hom initial)\n'
                  '      (Resources.run (fun i s => Resources.reweight hom (transition i s)) xs) :=\n'
                  '  InterpretationAssistance.seeded_reweight hom initial transition xs\n')
        retained = ['initial', 'transition', 'weight']
    else:
        raise ValueError('unsupported route schema: ' + schema)
    base = header + declarations
    for i, (_, proposition) in enumerate(requirements):
        base += f'def requirement_{i} : Prop := {proposition}\n#transport_requirement Requested.requirement_{i}\n'
    # A local checked root exists even when the route has no extra requirements.
    base += 'def requestPresent : Unit := ()\n'
    if schema in {'extension', 'image'}:
        available = ['selectedSource.code', 'selectedSource.witness',
                     'route.code selectedSource.code', 'route.value selectedSource.witness']
    else:
        available = retained
    base += '\n'.join('#check ' + term for term in available) + '\n'
    return base, requirements, result, retained, available


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('route')
    p.add_argument('--registry', type=Path, default=DEFAULT)
    p.add_argument('--out', type=Path, required=True, help='new immutable receipt directory')
    p.add_argument('--certificate', action='append', default=[], metavar='OBLIGATION=DECLARATION')
    p.add_argument('--support', type=Path, help='trusted author Lean declarations, included in every request snapshot')
    p.add_argument('--budget', type=Path, default=os.environ.get('CONALED_TRIAL_BUDGET'), help='coordinator-initialized external per-arm trial state')
    p.add_argument('--omit', action='append', default=[], metavar='OBLIGATION')
    args = p.parse_args()
    args.out.mkdir(parents=True, exist_ok=False)
    record = {'route': args.route, 'started': now(), 'checks': [], 'status': 'checker failure'}

    def finish(status, detail):
        record.update(status=status, detail=detail, finished=now())
        (args.out / 'receipt.json').write_text(json.dumps(record, indent=2) + '\n')
        print(json.dumps(record, indent=2))
        return 0 if status == 'checked' else 2

    def check(label, source):
        path = args.out.resolve() / (label + '.lean')
        path.write_text(source + '\nend Requested\n')
        command = ([sys.executable, str(ROOT / 'scripts/interpretation-trial-check.py'),
                    '--state', str(args.budget.resolve()), '--source', str(path)]
                   if args.budget else ['lake', 'env', 'lean', '--json', str(path)])
        started = now()
        proc = subprocess.run(command, cwd=ROOT, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        log = args.out / (label + '.log')
        log.write_text(proc.stdout)
        record['checks'].append({'phase': label, 'command': command, 'source_sha256': digest(path.read_bytes()),
                                 'started': started, 'finished': now(), 'exit': proc.returncode, 'checker_started': proc.returncode not in (74, 75), 'log': str(log)})
        if proc.returncode == 75:
            raise BudgetExhausted('External trial budget exhausted; no further Lean process started.')
        if proc.returncode not in (0, 1):
            raise CheckerFailure(f'Checker process failed during {label} with exit {proc.returncode}; no evidence rejection is inferred.')
        if proc.returncode == 0 and 'TRANSPORT_AUDIT_OK' not in proc.stdout:
            raise CheckerFailure(f'Checker produced no audit confirmation during {label}.')
        if proc.returncode == 1:
            messages = []
            for line in proc.stdout.splitlines():
                try:
                    message = json.loads(line)
                except ValueError:
                    continue
                if isinstance(message, dict):
                    messages.append(message)
            if not any(message.get('severity') == 'error' for message in messages):
                raise CheckerFailure(f'Checker exited 1 without a Lean error diagnostic during {label}.')
        return proc.returncode == 0

    try:
        raw = args.registry.read_bytes()
        registry = json.loads(raw)
        record['registry_sha256'] = digest(raw)
        record['implementation_sha256'] = digest(Path(__file__).read_bytes())
        record['checker_source_sha256'] = digest((ROOT / 'SquareKit/InterpretationDiagnostics.lean').read_bytes())
        record['toolchain'] = (ROOT / 'lean-toolchain').read_text().strip()
        record['dependency_manifest_sha256'] = digest((ROOT / 'lake-manifest.json').read_bytes())
        record['git_head'] = subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=ROOT, text=True).strip()
        record['compiler'] = subprocess.check_output(['lean', '--version'], cwd=ROOT, text=True).strip()
        if record['toolchain'].split(':')[-1].lstrip('v') not in record['compiler']:
            return finish('checker failure', 'Compiler does not match pinned toolchain.')
        if args.route not in registry['routes']:
            return finish('registry exhausted', 'No registered route with this ID; no mathematical impossibility is claimed.')
        entry = registry['routes'][args.route]
        record['request'] = entry
        base, requirements, result, retained, available = render(entry)
        record['available_expressions'] = available
        if args.support:
            support = args.support.read_text()
            record['support_sha256'] = digest(support.encode())
            base = base.replace('namespace Requested\n', support + '\nnamespace Requested\n', 1)
        record['obligations'] = [{'id': key, 'requested_type': typ, 'declaration': f'Requested.requirement_{i}'}
                                  for i, (key, typ) in enumerate(requirements)]
        certificates = dict(entry.get('certificates', {}))
        valid_ids = {k for k, _ in requirements}
        for key in args.omit:
            if key not in valid_ids:
                raise ValueError('unknown obligation: ' + key)
            certificates.pop(key, None)
        for assignment in args.certificate:
            key, decl = assignment.split('=', 1)
            if key not in valid_ids or not re.fullmatch(r'[A-Za-z_][A-Za-z_0-9]*(\.[A-Za-z_][A-Za-z_0-9]*)*', decl):
                raise ValueError('certificate override requires a known obligation and qualified declaration name')
            certificates[key] = decl
        record['supplied_certificates'] = certificates
        if not check('requirements', base + '#transport_audit Requested.requestPresent\n'):
            return finish('checker failure', 'Request schema/imports failed checking; inspect requirements.log.')
        accepted = base
        missing = []
        for i, (key, _) in enumerate(requirements):
            if key not in certificates:
                refutation = entry.get('refutations', {}).get(key)
                if refutation:
                    source = base + f'theorem refuted : ¬ requirement_{i} := {refutation}\n#transport_audit Requested.refuted\n'
                    if not check('refutation_' + key, source):
                        return finish('checker failure', 'Registered refutation failed checking.')
                    return finish('refuted obligation', f'Checked negation of Requested.requirement_{i}; alternative routes/observations remain possible.')
                missing.append(key)
                continue
            declaration = f'theorem certificate_{i} : requirement_{i} := {certificates[key]}\n'
            if not check('certificate_' + key, base + declaration + f'#transport_audit Requested.certificate_{i}\n'):
                return finish('rejected evidence', f'Supplied certificate for {key} did not check and audit; no impossibility claim.')
            accepted += declaration
        if missing:
            return finish('missing evidence', 'No supplied certificate for: ' + ', '.join(missing))
        source = accepted + result + '\n'.join('#check ' + x for x in retained) + '\n#transport_audit Requested.result\n'
        record['retained_expressions'] = retained
        if not check('result', source):
            return finish('checker failure', 'Checked inputs did not produce an audited result; inspect generated schema application.')
        return finish('checked', 'Generated result and every local logical declaration passed Lean and the axiom audit. See result.lean and result.log.')
    except BudgetExhausted as error:
        return finish('budget exhausted', str(error))
    except (CheckerFailure, OSError, ValueError, KeyError, subprocess.CalledProcessError) as error:
        return finish('checker failure', str(error))


if __name__ == '__main__':
    sys.exit(main())
