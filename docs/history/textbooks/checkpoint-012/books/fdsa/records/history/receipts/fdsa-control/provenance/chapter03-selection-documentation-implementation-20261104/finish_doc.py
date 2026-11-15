from pathlib import Path
import difflib,hashlib
B=Path('/workspace/scratch/b4a17a285e23/fdsa-restored-20261104')
P=B/'fdsa-control/provenance/chapter03-selection-documentation-implementation-20261104'
p=B/'conaled-ch02-quicksort/docs/research/fdsa-selection.md'
old=p.read_text();assert hashlib.sha256(old.encode()).hexdigest()=='a70b9912cdd589e17ef6b71ea726dd9951920d955938e7ac9152abffdb1694f9'
changes={
'were preserved. Earlier failures and exact corrections remain recorded. The older random execution,\nexpectation, drift and tail sources':'were preserved. Earlier failures and exact corrections remain recorded. The\nolder random execution, expectation, drift and tail sources',
'The pure `Applications.Sequences.Chunks.chop` adapter reuses standard list splitting while\nexposing the source equations:':'The pure `Applications.Sequences.Chunks.chop` adapter reuses standard list\nsplitting while exposing the source equations:',
'Sizes3 and 4 give\ncoefficient1.':'Sizes 3 and 4 give\ncoefficient 1.',
'Size1 has an actual':'Size 1 has an actual',
'first genuinely\nrecursive scalar budgets.':'first\nrecursive scalar budgets.',
'validation must survive assembly and review. The table records mathematical domains and source-model\nlimits rather than promoting':'validation must survive assembly and review. The table records mathematical\ndomains and source-model limits rather than promoting',
'cutoff 20, toll19n+54;':'cutoff 20, toll 19n+54;',
'source tail threshold9(4+w)n+2':'source tail threshold 9(4+w)n+2'
}
new=old
for a,b in changes.items():
 assert new.count(a)==1,(a,new.count(a));new=new.replace(a,b)
patch=''.join(difflib.unified_diff(old.splitlines(True),new.splitlines(True),fromfile='v3/docs/research/fdsa-selection.md',tofile='final/docs/research/fdsa-selection.md'))
(P/'editorial-v3-final.patch').write_text(patch);p.write_text(new)
print(patch);print('FINAL_DOC',len(new.encode()),hashlib.sha256(new.encode()).hexdigest())
