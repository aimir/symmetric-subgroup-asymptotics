#!/usr/bin/env python3
"""Emit short normal-word proofs for one explicitly selected degree-eight source.

Reads the literal source and an already checked normal-state source. Does not
run Lean, GAP, a normal subgroup search, or any other exporter. Every emitted
word evaluation must be checked by Lean separately. No bulk mode.

Requires --root and --output-dir; never defaults to the formal source tree.
Receipts go to stdout and optionally an explicit --receipt outside --root.
The 8T16 output preserves the checked pilot module's historical name/header.
Bounds:128 source rows,32 normal states,8 ordinary seeds,3 million tiny
permutation compositions,30 seconds cooperative time,2 MiB per input/output.
These cooperative bounds do not replace the primary agent's capped Lean check.
"""
import argparse,itertools,re,time,hashlib
from pathlib import Path
ap=argparse.ArgumentParser();ap.add_argument('--master',choices=['8T'+str(i) for i in [1,2,3,4,5,6,7,8,9,10,11,15,16,17,18,19,20,21,26,27,28,29,30,31,35]],required=True);ap.add_argument('--root',type=Path,required=True);ap.add_argument('--output-dir',type=Path,required=True);ap.add_argument('--receipt',type=Path);a=ap.parse_args()
a.root=a.root.resolve();a.output_dir=a.output_dir.resolve()
if a.receipt and a.receipt.resolve().is_relative_to(a.root):ap.error('--receipt must be outside --root')
started=time.monotonic();ops=0
witnesses=[]
def read_bounded(path,limit):
 with path.open('rb') as stream:data=stream.read(limit+1)
 if len(data)>limit:raise RuntimeError('selected input byte cap exceeded')
 return data.decode('utf-8')
P=a.root/'formal/SymmetricSubgroupAsymptotics';e=tuple(range(8))
def mul(x,y):
 global ops
 ops+=1
 if ops>3000000 or time.monotonic()-started>30:raise RuntimeError('selected budget exceeded')
 return tuple(x[i] for i in y)
def inv(x):return tuple(x.index(i) for i in range(8))
def closure(gs):
 rows=[e];seen={e:[]}
 for x in rows:
  for j,g in enumerate(gs):
   y=mul(x,g)
   if y not in seen:
    assert len(rows)<128
    seen[y]=seen[x]+[j];rows.append(y)
 return rows,seen
srcpath=P/f'BinaryMenuCayley{a.master}.lean';src=read_bounded(srcpath,100000)
carrier=a.master in ['8T26','8T27','8T35']
missing=a.master in ['8T28','8T29','8T31']
sp=P/(f'GeneratedCarrierNormal{a.master}/States.lean' if carrier else f'GeneratedRDTNormal{a.master}/States.lean' if missing else f'GeneratedNormal8/States{a.master}.lean')
ss=read_bounded(sp,2000000)
ns='BinaryCarrierNormal' if carrier else 'RDTBinaryNormal' if missing else 'BinaryNormal'
ns+=a.master
stateimport=f'GeneratedCarrierNormal{a.master}.Registry' if carrier else f'GeneratedRDTNormal{a.master}.Registry' if missing else f'GeneratedNormal8.Registry{a.master}'
gs=[tuple(map(int,x.split(','))) for x in re.findall(r'toFun x := \(#\[([0-9,]+)\]',src)]
assert 1<=len(gs)<=5
G,_=closure(gs);G.sort(key=lambda x:sum(z*8**i for i,z in enumerate(x)));idx={x:i for i,x in enumerate(G)}
normaldata=[]
for i,r,body in re.findall(r'namespace N(\d+)\ndef normalGenerators \(j : Fin (\d+)\) : Source := (.*?)\ndef kernel',ss,re.S):
 i,r=int(i),int(r);assert r<=8 and i==len(normaldata)
 if r==0:inds=[]
 elif r==1:inds=[int(re.search(r'⟨\(*\s*(\d+)',body)[1])]
 else:inds=list(map(int,re.findall(r'(?:then|else) (\d+)',body)))
 assert len(inds)==r,(i,r,inds)
 normaldata.append([G[j] for j in inds])
assert 1<=len(normaldata)<=32
suffix=('Pilot' if a.master=='8T16' else '')+a.master
out=['import SymmetricSubgroupAsymptotics.RDTDegreeEightNormalWords',f'import SymmetricSubgroupAsymptotics.{stateimport}']+([''] if a.master=='8T16' else ['','/-! One selected source: actual ambient normal generation from checked words. -/',''])+['set_option autoImplicit false','set_option maxRecDepth 100000','noncomputable section','open scoped Classical',f'namespace SymmetricSubgroupAsymptotics.RDTDegreeEightNormalWords{suffix}',f'open {ns}',f'local instance : Group Source := BinaryMenuCayley{a.master}.group','']
for i,ng in enumerate(normaldata):
 r=len(ng)
 if r<=3:
  out += [f'theorem normal_bound_{i} : MarkedC4.normalGen N{i}.kernel ≤ 3 :=',f'  (RDTDegreeEightNormalWords.normalGen_le_of_closure_tuple N{i}.kernel',f'    N{i}.normalGenerators N{i}.state.generated).trans (by decide)','']
  continue
 for k in range(1,4):
  result=None
  for selected in itertools.combinations(range(r),k):
   letters=[(g,j) for g in G for j in range(k)]
   conj=[mul(mul(g,ng[selected[j]]),inv(g)) for g,j in letters]
   rows,ws=closure(conj)
   if all(x in ws for x in ng):result=(selected,letters,ws);break
  if result:break
 assert result is not None,(a.master,i,'no three-seed tuple')
 selected,letters,ws=result
 out += [f'private def selected{i} : Fin {k} → Fin {r} := !['+','.join(map(str,selected))+']',f'private def words{i} : Fin {r} → List (Source × Fin {k}) := ![']
 for j,x in enumerate(ng):
  pairs=[letters[t] for t in ws[x]]
  out += ['  ['+','.join(f'(⟨{idx[g]}⟩,{h})' for g,h in pairs)+('],' if j<r-1 else ']]')]
 out += [f'private theorem words{i}_checked : ∀ j,',f'    RDTDegreeEightNormalWords.eval (N{i}.normalGenerators ∘ selected{i}) (words{i} j) =',f'      N{i}.normalGenerators j := by decide +kernel',f'theorem normal_bound_{i} : MarkedC4.normalGen N{i}.kernel ≤ 3 :=',f'  (RDTDegreeEightNormalWords.normalGen_le_of_words N{i}.kernel',f'    N{i}.normalGenerators N{i}.state.generated selected{i} words{i} words{i}_checked).trans (by decide)','']
 witnesses.append({'state':i,'ordinary_seeds':r,'normal_seeds':k,'word_lengths':[len(ws[x]) for x in ng]})
out += ['theorem all_normal_bound (N : Subgroup Source) [N.Normal] :', '    MarkedC4.normalGen N ≤ 3 := by','  obtain ⟨i,rfl⟩ := complete N','  fin_cases i']+[f'  · exact normal_bound_{i}' for i in range(len(normaldata))]+['',f'end SymmetricSubgroupAsymptotics.RDTDegreeEightNormalWords{suffix}','','end','']
a.output_dir.mkdir(parents=True,exist_ok=True)
path=a.output_dir/f'RDTDegreeEightNormalWords{suffix}.lean'
payload='\n'.join(out)
if len(payload.encode())>2000000:raise RuntimeError('selected output byte cap exceeded')
path.write_text(payload)
receipt={'master':a.master,'output':str(path),'operations':ops,'bytes':path.stat().st_size,
 'seconds':time.monotonic()-started,'source_sha256':hashlib.sha256(src.encode()).hexdigest(),
 'states_sha256':hashlib.sha256(ss.encode()).hexdigest(),'output_sha256':hashlib.sha256(payload.encode()).hexdigest(),
 'witnesses':witnesses}
import json
receipt_text=json.dumps(receipt,sort_keys=True,indent=2)+'\n'
if a.receipt:
 a.receipt.parent.mkdir(parents=True,exist_ok=True)
 a.receipt.write_text(receipt_text)
print(receipt_text,end='')
