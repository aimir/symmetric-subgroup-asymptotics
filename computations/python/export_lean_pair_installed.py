#!/usr/bin/env python3
"""Install all width-eight pair certificates on their original physical actions.

The original subgroup, original normal, frame, central cut, quotient map,
fixed capacity, and physical width are bound in one Lean construction.
Character and exceptional-transport normal indices remain explicit branches.
"""
from pathlib import Path
import argparse,gzip,json
from export_lean_normal_registry import ROOT,finfun
OUT=ROOT/'formal/SymmetricSubgroupAsymptotics/GeneratedPair8'

def emit(node,record):
    label=node['id'][1:].replace('_','T');m=len(record['normals']);ps=[i for i,x in enumerate(record['normals']) if x['kind']=='pair'];rs=[i for i,x in enumerate(record['normals']) if x['kind']!='pair'];p=len(ps);d=len(node['generators'])
    index_expr='Fin.elim0'; cert_expr='(fun i => Fin.elim0 i)'
    for i in reversed(ps):
        index_expr=f'(Fin.cases ({i} : Fin {m}) {index_expr})'
        cert_expr=f'(Fin.cases (BinaryPairLocal{label}.N{i}.certificate.transport BinaryMenuCayley{label}.originalEquiv) {cert_expr})'
    s=f'''import SymmetricSubgroupAsymptotics.BinaryPairCertificateCapacity
import SymmetricSubgroupAsymptotics.GeneratedPair8.Local{label}

/-! Every pair record for {label}, installed on the literal original
permutation subgroup with its retained original normal and physical width.
The residual character/transport indices remain an explicit branch. -/
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryPairInstalled{label}
local instance : Group BinaryNormal{label}.Source := BinaryMenuCayley{label}.group
abbrev Original := Subgroup.closure (Set.range BinaryMenuCayley{label}.generators)
abbrev frame := BinaryPair{label}.Frame0.physicalFrame

def generators (j : Fin {d}) : Original :=
  BinaryMenuCayley{label}.originalEquiv (BinaryNormal{label}.generators j)
theorem generators_full : Subgroup.closure (Set.range generators)=⊤ := by
  have h := congrArg (Subgroup.map BinaryMenuCayley{label}.originalEquiv.toMonoidHom)
    BinaryNormal{label}.generators_full
  rw [MonoidHom.map_closure] at h
  have ht := Subgroup.map_top_of_surjective BinaryMenuCayley{label}.originalEquiv.toMonoidHom
    BinaryMenuCayley{label}.originalEquiv.surjective
  have he : BinaryMenuCayley{label}.originalEquiv.toMonoidHom '' Set.range BinaryNormal{label}.generators=
      Set.range generators := by ext x; simp [generators]
  rw [he] at h
  exact h.trans ht
theorem original_isPGroup : IsPGroup 2 Original :=
  BinaryNormal{label}.source_isPGroup.of_surjective
    BinaryMenuCayley{label}.originalEquiv.toMonoidHom BinaryMenuCayley{label}.originalEquiv.surjective

def pairIndices : Fin {p} → Fin {m} := {index_expr}
def residualIndices : List (Fin {m}) := [{','.join(map(str,rs))}]
theorem index_coverage (i : Fin {m}) :
    i∈residualIndices ∨ ∃ j, pairIndices j=i := by revert i; decide +kernel

def physicalNormal (j : Fin {p}) : Subgroup Original :=
  (BinaryNormal{label}.states (pairIndices j)).kernel.map BinaryMenuCayley{label}.originalEquiv.toMonoidHom
instance physicalNormal_normal (j : Fin {p}) : (physicalNormal j).Normal :=
  Subgroup.Normal.map inferInstance _ BinaryMenuCayley{label}.originalEquiv.surjective

def physicalCertificates : (j : Fin {p}) →
    BinaryPairLocalCertificate generators frame.top (physicalNormal j) :=
  {cert_expr}
'''+f'''
theorem physical_width (j : Fin {p}) :
    (physicalCertificates j).width=Nat.card (Fin 8) := by
  rw [Nat.card_fin]
  fin_cases j <;> rfl

def physicalCut (j : Fin {p}) := sectionSubgroupImage (p := 2)
  (V := frame.kernelSpace ⧸ frame.normalSpace (physicalNormal j))
  (frame.sectionMap (physicalNormal j)) ((physicalCertificates j).kernelCut frame)

theorem physical_cutDimension (j : Fin {p}) :
    Module.finrank (ZMod 2) (physicalCut j)=(physicalCertificates j).cutDimension :=
  (physicalCertificates j).cutDimension_eq frame (physicalNormal j)

/-- The exact capacity is for the retained original quotient action after
its retained actual central cut. -/
theorem physical_capacity (j : Fin {p}) :
    representationSchurCapacity ((physicalCertificates j).physicalRepresentation
      frame (physicalNormal j) generators generators_full)=
        ((physicalCertificates j).fixedDimension:ℝ) :=
  (physicalCertificates j).capacity_eq frame (physicalNormal j) generators
    generators_full original_isPGroup

/-- The numerical gap is now tied to the actual eight physical points. -/
theorem physical_gap (j : Fin {p}) :
    ((physicalCertificates j).coverDegree:ℝ)+2*(physicalCertificates j).cutDimension+
      4*representationSchurCapacity ((physicalCertificates j).physicalRepresentation
        frame (physicalNormal j) generators generators_full)<8 := by
  have h := (physicalCertificates j).physical_gap frame (physicalNormal j) generators
    generators_full original_isPGroup (physical_width j)
  simpa only [Nat.card_fin] using h

theorem physical_gap_actual (j : Fin {p}) :
    ((physicalCertificates j).coverDegree:ℝ)+2*Module.finrank (ZMod 2) (physicalCut j)+
      4*representationSchurCapacity ((physicalCertificates j).physicalRepresentation
        frame (physicalNormal j) generators generators_full)<8 := by
  rw [physical_cutDimension]
  exact physical_gap j

/-- Every original normal enters a fully installed pair certificate or one
of the explicitly retained character/transport normal rows. -/
theorem normal_coverage (N : Subgroup Original) [N.Normal] :
    (∃ j, physicalNormal j=N) ∨
      ∃ i∈residualIndices, (BinaryNormal{label}.states i).kernel.map
        BinaryMenuCayley{label}.originalEquiv.toMonoidHom=N := by
  obtain ⟨i,hi⟩ := BinaryNormal{label}.registry.complete_map_of_equiv
    BinaryNormal{label}.source_isPGroup BinaryMenuCayley{label}.originalEquiv N
  rcases index_coverage i with hr|⟨j,hj⟩
  · exact Or.inr ⟨i,hr,hi⟩
  · exact Or.inl ⟨j,by simpa only [physicalNormal,hj] using hi⟩
end SymmetricSubgroupAsymptotics.BinaryPairInstalled{label}
'''
    return OUT/f'Installed{label}.lean',s

def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--node',action='append');ap.add_argument('--check',action='store_true');args=ap.parse_args()
    with gzip.open(ROOT/'certificates/data/binary_menu.jsonl.gz','rt') as f:
        meta=json.loads(next(f));records={x['id']:x for line in f if (x:=json.loads(line)).get('kind')=='action'}
    nodes={n['id']:n for n in meta['nodes']};selected=args.node or [k for k,n in nodes.items() if n['degree']==8 and records[k]['normals']]
    for name in selected:
        path,s=emit(nodes[name],records[name]);b=s.encode()
        if args.check:
            if not path.exists() or path.read_bytes()!=b:raise SystemExit(f'Stale generated file {path}')
        elif not path.exists() or path.read_bytes()!=b:path.write_bytes(b)
        print(path.relative_to(ROOT),flush=True)
if __name__=='__main__':main()
