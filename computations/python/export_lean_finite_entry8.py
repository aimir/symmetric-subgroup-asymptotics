#!/usr/bin/env python3
"""Combine all 203 actual width-eight normal records into finite-entry coverage.

This is finite-entry coverage, not the analytic character/fusion theorem.
The original normal and normalizer survive the one ambient conjugation.
"""
import argparse,gzip,json
from pathlib import Path
from export_lean_normal_registry import ROOT
OUT=ROOT/'formal/SymmetricSubgroupAsymptotics/GeneratedPair8'

def emit(node,record):
 label=node['id'][1:].replace('_','T');d=len(node['generators']);normals=record['normals']
 s=f'import SymmetricSubgroupAsymptotics.BinaryNormalFiniteEntry8\nimport SymmetricSubgroupAsymptotics.GeneratedPair8.Installed{label}\n'
 if any(x['kind']=='character' for x in normals):s+=f'import SymmetricSubgroupAsymptotics.GeneratedCharacter8.Characters{label}\n'
 s+=f'''
/-! All original normal states of {label} enter their checked finite branch.
Character counting and the whole-family weighted sum remain separate. -/
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryFiniteEntry{label}
local instance : Group BinaryNormal{label}.Source := BinaryMenuCayley{label}.group
abbrev Original := BinaryPairInstalled{label}.Original

/-- No semantic acceptance or normal-enumeration premise is required. -/
theorem finiteEntryCoverage (N : Subgroup Original) [N.Normal] : BinaryFiniteEntry8 Original N := by
  rcases BinaryPairInstalled{label}.normal_coverage N with ⟨j,rfl⟩|⟨i,hi,he⟩
  · exact Or.inl ⟨{{
      pairCount := 4
      frame := BinaryPairInstalled{label}.frame
      generatorCount := {d}
      generators := BinaryPairInstalled{label}.generators
      generators_full := BinaryPairInstalled{label}.generators_full
      localCertificate := BinaryPairInstalled{label}.physicalCertificates j
      physical_width := BinaryPairInstalled{label}.physical_width j }}⟩
  · fin_cases i
'''
 for i,nr in enumerate(normals):
  if nr['kind']=='pair':s+=f'''    · exact False.elim ((by decide +kernel : ¬({i} : Fin {len(normals)})∈BinaryPairInstalled{label}.residualIndices) hi)
'''
  elif nr['kind']=='character':s+=f'''    · cases he
      exact Or.inr (Or.inl ⟨BinaryNormalCharacters{label}.N{i}.physicalCriterion⟩)
'''
  elif nr['kind']=='transport':
   k=[16,20,21].index(int(node['id'].split('_')[1]))
   s+=f'''    · cases he
      exact Or.inr (Or.inr ⟨{k},BinaryNormalTransport{label}.source_eq,
        BinaryNormalTransport{label}.axis_eq⟩)
'''
  else:raise ValueError(nr['kind'])
 s+=f'end SymmetricSubgroupAsymptotics.BinaryFiniteEntry{label}\n'
 return OUT/f'Entry{label}.lean',s

def aggregate(nodes,records):
 names=[k for k,n in nodes.items() if n['degree']==8];nonbase=[k for k in names if records[k]['normals']]
 s='import SymmetricSubgroupAsymptotics.BinaryNormalCoverage8\n'
 for name in nonbase:s+=f'import SymmetricSubgroupAsymptotics.GeneratedPair8.Entry{name[1:].replace("_","T")}\n'
 s+='''
/-! Complete finite-entry coverage in width eight. All 203 nonbase normal
records are installed; the eight existing base action indices stay explicit.
This is not an analytic character-owner or global weighted-sum theorem. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryFiniteEntryCoverage8
open BinaryNormalCoverage8 BinaryActionRegistry8
open scoped Pointwise

theorem finiteEntryCoverage (i : Fin 26) (hi : i∉baseIndices)
    (N : Subgroup (actions i)) [hN : N.Normal] : BinaryFiniteEntry8 (actions i) N := by
  fin_cases i
'''
 for name in names:
  label=name[1:].replace('_','T')
  if name in nonbase:s+=f'  · exact @BinaryFiniteEntry{label}.finiteEntryCoverage N hN\n'
  else:s+='  · exact False.elim (hi (by decide +kernel))\n'
 s+='''
/-- One original ambient conjugation preserves the specified normal and
original normalizer while placing it in its checked finite branch. -/
theorem complete (H : Subgroup (Equiv.Perm (Fin 8))) (hH : IsPGroup 2 H)
    (ht : PermutationSubgroupTransitive H) (N : Subgroup H) [N.Normal] :
    ∃ i : Fin 26, ∃ g : Equiv.Perm (Fin 8), ∃ hg : MulAut.conj g • H=actions i,
      (i∈baseIndices ∨ BinaryFiniteEntry8 (actions i) (actionConjugacyNormal g hg N)) ∧
      Nat.card (Subgroup.normalizer (H:Set (Equiv.Perm (Fin 8))))=
        Nat.card (Subgroup.normalizer (actions i:Set (Equiv.Perm (Fin 8)))) := by
  obtain ⟨i,g,hg⟩ := BinaryActionRegistry8.complete H hH ht
  refine ⟨i,g,hg,?_,actionConjugacy_normalizer_card g hg⟩
  by_cases hi : i∈baseIndices
  · exact Or.inl hi
  · exact Or.inr (finiteEntryCoverage i hi (actionConjugacyNormal g hg N))
end SymmetricSubgroupAsymptotics.BinaryFiniteEntryCoverage8
'''
 return ROOT/'formal/SymmetricSubgroupAsymptotics/BinaryFiniteEntryCoverage8.lean',s

def main():
 ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--node',action='append');ap.add_argument('--check',action='store_true');args=ap.parse_args()
 with gzip.open(ROOT/'certificates/data/binary_menu.jsonl.gz','rt') as f:
  meta=json.loads(next(f));records={x['id']:x for line in f if (x:=json.loads(line)).get('kind')=='action'}
 nodes={n['id']:n for n in meta['nodes']};selected=args.node or [k for k,n in nodes.items() if n['degree']==8 and records[k]['normals']]
 outputs=[emit(nodes[name],records[name]) for name in selected]
 if args.node is None:outputs.append(aggregate(nodes,records))
 for path,s in outputs:
  b=s.encode()
  if args.check:
   if not path.exists() or path.read_bytes()!=b:raise SystemExit(f'Stale generated file {path}')
  elif not path.exists() or path.read_bytes()!=b:path.write_bytes(b)
  print(path.relative_to(ROOT),flush=True)
if __name__=='__main__':main()
