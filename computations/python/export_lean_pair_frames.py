#!/usr/bin/env python3
"""Export shared physical pair frames for every width-8 pair source.

Frame bijections, source-row top maps, generator transitions and pointwise
intertwining are all checked by Lean. The resulting flip space is the
actual kernel image, not the whole coordinate space.
"""
from pathlib import Path
import argparse,gzip,json
from export_lean_menu_cayley import table,packed,lookup,checks
from export_lean_normal_registry import unpack,perm,arr,inv,fun,finfun
ROOT=Path(__file__).resolve().parents[2]
OUT=ROOT/'formal/SymmetricSubgroupAsymptotics/GeneratedPair8'

def emit(node,records):
    label=node['id'][1:].replace('_','T');w=node['degree'];assert w==8
    frames=sorted({tuple(map(tuple,n['frame'])) for n in records['normals'] if n['kind']=='pair'})
    gs=list(map(perm,node['generators']));st=table(gs,w);source=[unpack(c,w) for c in st['codes']];n=len(source);d=len(gs)
    s=f'''import SymmetricSubgroupAsymptotics.BinaryPairFrames
import SymmetricSubgroupAsymptotics.FiniteCayleyMaps
import SymmetricSubgroupAsymptotics.BinaryMenuCayley{label}

/-! Shared actual physical pair frames for {label}. Generated from the
original frame and original source permutations. Kernel checks bind all
point actions; BinaryPairFrame proves the reversible actual flip chart. -/
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryPair{label}
abbrev Source := FiniteGroupRow {n}
local instance : Group Source := BinaryMenuCayley{label}.group

'''
    for fi,fr in enumerate(frames):
        points=[x-1 for pair in fr for x in pair];pair={x:i//2 for i,x in enumerate(points)};bit={x:i%2 for i,x in enumerate(points)}
        tops=[tuple(pair[g[fr[i][0]-1]] for i in range(4)) for g in source]
        distinct=sorted(set(tops),key=packed);topIndex=[distinct.index(t) for t in tops]
        images=[distinct.index(tuple(pair[g[fr[i][0]-1]] for i in range(4))) for g in gs]
        s+=f'''namespace Frame{fi}
def frame : Fin 4 × ZMod 2 ≃ Fin 8 where
  toFun p := ({arr(points)} : Array (Fin 8))[2*p.1.val+p.2.val]!
  invFun x := (({arr([pair[x] for x in range(8)])} : Array (Fin 4))[x.val]!,
    ({arr([bit[x] for x in range(8)])} : Array (ZMod 2))[x.val]!)
  left_inv := by decide +kernel
  right_inv := by decide +kernel

'''
        for j,t in enumerate(distinct):
            s+=f'''private def top{j} : Equiv.Perm (Fin 4) where
  toFun x := ({arr(t)} : Array (Fin 4))[x.val]!
  invFun x := ({arr(inv(t))} : Array (Fin 4))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

'''
        s+=f'''private def values (i : Fin {n}) : Equiv.Perm (Fin 4) :=
  {lookup([f'top{x}' for x in topIndex])}
private def images (j : Fin {d}) : Equiv.Perm (Fin 4) :=
  {lookup([f'top{x}' for x in images],'j.val')}
private theorem step_checked : ∀ i j,
    values (BinaryMenuCayley{label}.certificate.next i j)=values i*images j := {checks(n)}
private theorem identity_checked : values BinaryMenuCayley{label}.certificate.identity=1 := by decide +kernel

def topHom : Source →* Equiv.Perm (Fin 4) where
  toFun u := values u.index
  map_one' := identity_checked
  map_mul' u v := by
    change values (BinaryMenuCayley{label}.certificate.walk u.index
      (BinaryMenuCayley{label}.certificate.words v.index))=values u.index*values v.index
    rw [EncodedCayleyCertificate.values_walk _ values images step_checked,
      ← EncodedCayleyCertificate.values_word _ values images step_checked identity_checked]

private theorem frame_checked : ∀ i : Fin {n}, ∀ p : Fin 4 × ZMod 2,
    (frame.symm (finFunctionFinEquiv.symm (BinaryMenuCayley{label}.certificate.rows i) (frame p))).1=
      values i p.1 := {checks(n)}

/-- The exact original source, its exact pair action, and all original points. -/
def physicalFrame : BinaryPairFrame
    (Subgroup.closure (Set.range BinaryMenuCayley{label}.generators)) (Fin 4) :=
  BinaryPairFrame.ofEquiv BinaryMenuCayley{label}.originalEquiv topHom frame (by
    intro u p
    change (frame.symm (BinaryMenuCayley{label}.certificate.toCayley.elements u.index (frame p))).1=
      values u.index p.1
    rw [binaryPair_source_row_apply]
    exact frame_checked u.index p)

/-- The canonical binary chart retains the literal physical kernel. -/
def kernelChart : physicalFrame.top.ker ≃* Multiplicative physicalFrame.kernelSpace :=
  physicalFrame.kernelChart

end Frame{fi}

'''
    s+=f'end SymmetricSubgroupAsymptotics.BinaryPair{label}\n'
    return OUT/f'Frames{label}.lean',s

def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--node',action='append');ap.add_argument('--check',action='store_true');args=ap.parse_args()
    with gzip.open(ROOT/'certificates/data/binary_menu.jsonl.gz','rt') as f:
        meta=json.loads(next(f)); records={x['id']:x for line in f if (x:=json.loads(line)).get('kind')=='action'}
    nodes={n['id']:n for n in meta['nodes']};names=args.node or [k for k,n in nodes.items() if n['degree']==8 and any(r['kind']=='pair' for r in records[k]['normals'])]
    OUT.mkdir(exist_ok=True)
    for name in names:
        path,s=emit(nodes[name],records[name]);b=s.encode()
        if args.check:
            if not path.exists() or path.read_bytes()!=b:raise SystemExit(f'Stale generated file {path}')
        elif not path.exists() or path.read_bytes()!=b:path.write_bytes(b)
        print(path.relative_to(ROOT))
if __name__=='__main__':main()
