import hashlib
import json
import re
import subprocess
from datetime import datetime, timezone
from pathlib import Path
from urllib.parse import unquote, urlsplit

repo = Path('/tmp/conaled-314-320/316')
reviews = repo.parent / 'reviews'
old = 'ca54f31646bd60e1866efc39f257db5b27dc17fc'
base = 'f0773fee8fa40214c67606c46ba8c41eed8e674b'
candidate = 'd7d2beeea699bccc2f7eb0fee7f8fa52e6718186'
original_base = '9b0a0fe143c6f97f399632d4bb34a179db012181'
exp = repo / 'experiments/dependent-higher-identity'
run = repo.parent / '316-agda/final-316'

def git(*args):
    return subprocess.check_output(['git', '-C', str(repo), *args], text=True).strip()

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

assert git('rev-parse', 'HEAD') == candidate
assert git('branch', '--show-current') == 'research/dependent-higher-316'
assert not git('status', '--porcelain=v1')
assert git('show', '-s', '--format=%P', candidate).split() == [old, base]
git('merge-base', '--is-ancestor', base, candidate)
paths = git('diff', '--name-only', original_base, old).splitlines()
assert paths == git('diff', '--name-only', base, candidate).splitlines()
blobs = {}
for path in paths:
    before = git('rev-parse', old + ':' + path)
    after = git('rev-parse', candidate + ':' + path)
    assert before == after, path
    blobs[path] = {'git_blob': after, 'sha256': sha(repo / path)}
unchanged = ['docs/history', 'docs/research/dependent-coherence-discovery/292-external-memo.md',
             'flake.nix', 'flake.lock', '.envrc', 'lean-toolchain', 'lakefile.toml', 'lake-manifest.json']
for path in unchanged:
    assert not git('diff', old, candidate, '--', path), path
git('diff', base + '...HEAD', '--check')
receipt = json.loads((exp / 'validation.json').read_text())
assert receipt['exit_code'] == receipt['checker_receipt']['exit_code'] == 0
assert receipt['fresh_project_and_library_interfaces'] is True
for name, digest in receipt['input_hashes'].items():
    assert sha(exp / name) == digest, name
assert sha(exp / 'check.log') == receipt['log_sha256']
assert sha(exp / 'imports.dot') == receipt['dependency_graph_sha256']
for name in ['validation.json', 'check.log', 'imports.dot']:
    assert sha(exp / name) == sha(run / name), name
closure = receipt['checked_modules'] | receipt['builtin_modules']
assert len(closure) == receipt['import_closure_module_count'] == 235
assert len(receipt['checked_modules']) == receipt['checked_module_count'] == 229
assert set(re.findall(r'label="([^"]+)"', (exp / 'imports.dot').read_text())) == set(closure)
roots = {'source': run / 'source',
         'cubical': run / 'myers-agda-checkpoint/dependencies/cubical-0.9',
         'compiler-data': run / 'state/data'}
for module, item in closure.items():
    prefix, relative = item['path'].split('/', 1)
    assert sha(roots[prefix] / relative) == item['sha256'], module
archive = repo / 'docs/history/orbifold/agda-checkpoints/myers-orbifolds-agda-checkpoint-022.tar.gz'
assert sha(archive) == receipt['checkpoint_sha256']
compiler_archive = repo.parent / '316-agda/state/Agda-v2.8.0.2-linux.tar.xz'
assert sha(compiler_archive) == receipt['compiler_pins']['archive_sha256']
assert sha(run / 'state/bin/agda') == receipt['compiler_pins']['binary_sha256']
setup = json.loads((run / 'state/receipt.json').read_text())
assert setup['pins'] == receipt['compiler_pins']
for item in receipt['builtin_modules'].values():
    relative = item['path'].removeprefix('compiler-data/')
    assert setup['setup_files']['data/' + relative] == item['sha256']
links = []
for path in paths:
    if not path.endswith('.md'):
        continue
    for target in re.findall(r'\[[^\]]*\]\(([^)]+)\)', (repo / path).read_text()):
        target = target.strip('<>')
        url = urlsplit(target)
        if url.scheme or target.startswith('#'):
            continue
        resolved = (repo / path).parent / unquote(url.path)
        assert resolved.exists(), (path, target)
        links.append({'document': path, 'target': target})
compile((exp / 'check.py').read_text(), str(exp / 'check.py'), 'exec')
subprocess.run(['python3', str(exp / 'check.py'), '--help'], check=True, stdout=subprocess.DEVNULL)
assert not git('status', '--porcelain=v1')
record = {
    'result': 'passed', 'completed_utc': datetime.now(timezone.utc).isoformat(),
    'candidate': candidate, 'tree': git('rev-parse', 'HEAD^{tree}'), 'review_base': base,
    'validated_premerge_candidate': old, 'merge_conflicts': False,
    'authored_files_unchanged': blobs, 'unchanged_input_paths': unchanged,
    'reused_receipt_sha256': sha(exp / 'validation.json'),
    'reused_check_completed_utc': receipt['completed_utc'],
    'rechecked_closure_modules': len(closure), 'checked_modules': 229,
    'checkpoint_sha256': sha(archive), 'compiler_archive_sha256': sha(compiler_archive),
    'compiler_binary_sha256': sha(run / 'state/bin/agda'),
    'local_links_checked': links, 'diff_check': 'passed', 'python_compile_and_help': 'passed',
    'clean_checkout': True, 'validation_script_sha256': sha(Path(__file__)),
    'scope': 'Artifact identity supports reuse of the successful fresh Agda check; no new Agda or Lean build was run.'
}
output = reviews / ('316-validation-' + candidate + '.json')
with output.open('x') as stream:
    json.dump(record, stream, indent=2)
    stream.write('\n')
output.chmod(0o444)
print(json.dumps({'result': 'passed', 'candidate': candidate, 'unchanged_authored_files': len(blobs),
                  'closure_modules': len(closure), 'local_links': len(links), 'record': str(output)}, indent=2))
