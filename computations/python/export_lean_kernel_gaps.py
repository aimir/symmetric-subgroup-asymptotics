#!/usr/bin/env python3
"""Export complete shared width-sixteen joint axis/top numerical dichotomies.

All finite cells are checked: strict gap, or one explicitly listed axis
with the literal trivial top kernel. Only eight shared exceptional cells
remain, corresponding to21 original character/transport contexts.
"""
import argparse,json
from pathlib import Path
from export_lean_menu_cayley import ROOT,lookup
from export_lean_kernel_axes import act,basis,span,fixed_factors
OUT=ROOT/'formal/SymmetricSubgroupAsymptotics/GeneratedKernelAxes'

def exceptional_axes(t,m):
 bad=[]
 for i,a in enumerate(m['axes']):
  c=m['axes'][m['cuts'][i]];d=m['axes'][m['fixed'][i]];cost=2*(len(c)-len(a))+4*(len(d)-len(c))
  for j in range(len(t['normals'])):
   if cost+t['degrees'][j]>=16:
    assert j==0 and len(t['normals'][j])==1
    bad.append(i)
 return bad

def central_data(t,m,faithful_only=True):
 """Exceptional axes whose original quotient centre lies in the flip kernel."""
 result=[];kk=span(m['kernel_basis'])
 for ai in exceptional_axes(t,m):
  a=m['axes'][ai];aa=span(a)
  trivial=[p for p in t['rows'] if all(act(p,v)^v in aa for v in m['kernel_basis'])]
  if faithful_only and (len(trivial)!=1 or tuple(trivial[0])!=tuple(range(m['width']))):continue
  d=basis(v for v in kk if all(act(p,v)^v in aa for p in t['generators']))
  di=next(i for i,x in enumerate(m['axes']) if tuple(x)==d)
  result.append((ai,di,len(d)-len(a)))
 return result

def emit(t,m):
 mid=m['id'];sid=t['id'];n=len(m['axes']);q=len(t['normals']);bad=exceptional_axes(t,m)
 criterion=' ∨ '.join(f'i={i}' for i in bad) if bad else 'False'
 return f'''
namespace SymmetricSubgroupAsymptotics.BinaryKernelGaps{mid:03d}
open BinaryKernelAxes{mid:03d} BinaryKernelCuts{mid:03d}
local instance : Group Source := BinaryTopSource{sid:03d}.group

def exceptionalAxis (i : Fin {n}) : Prop := {criterion}

instance (i : Fin {n}) : Decidable (exceptionalAxis i) := by
  unfold exceptionalAxis
  infer_instance

/-- Every shared finite joint cell satisfies the gap or has trivial top;
compatibility is not needed for this stronger numerical assertion. -/
private theorem numerical : ∀ (i : Fin {n}) (j : Fin {q}),
    (BinaryTopRegistry{sid:03d}.states j).degree+cost i<16 ∨
      exceptionalAxis i ∧ j=0 := by decide +kernel

theorem bottom_kernel : (BinaryTopRegistry{sid:03d}.states 0).kernel=⊥ := by
  ext x
  exact ((BinaryTopRegistry{sid:03d}.states 0).mask_eq x).symm.trans
    (BinaryTopRegistry{sid:03d}.registry.bottom_mask x)

theorem gap_or_trivial_top (i : Fin {n}) (j : Fin {q}) :
    (BinaryTopRegistry{sid:03d}.states j).degree+cost i<16 ∨
      exceptionalAxis i ∧ (BinaryTopRegistry{sid:03d}.states j).kernel=⊥ := by
  rcases numerical i j with h|⟨h,rfl⟩
  · exact Or.inl h
  · exact Or.inr ⟨h,bottom_kernel⟩

theorem original_bottom_kernel : (BinaryTopRegistry{sid:03d}.originalStates 0).kernel=⊥ := by
  change ((BinaryTopRegistry{sid:03d}.states 0).transport BinaryTopSource{sid:03d}.originalEquiv).kernel=⊥
  rw [BinaryTopKernelData.transport_kernel,bottom_kernel,Subgroup.map_bot]

theorem gap_or_original_trivial_top (i : Fin {n}) (j : Fin {q}) :
    (BinaryTopRegistry{sid:03d}.originalStates j).degree+cost i<16 ∨
      exceptionalAxis i ∧ (BinaryTopRegistry{sid:03d}.originalStates j).kernel=⊥ := by
  rcases numerical i j with h|⟨h,rfl⟩
  · exact Or.inl h
  · exact Or.inr ⟨h,original_bottom_kernel⟩

/-- Independently complete invariant-axis and top-normal registries cover
all mathematical joint states, including every possible original lift. -/
theorem complete_joint_states (W : Subrepresentation action)
    (hW : W.toSubmodule≤kernel.toSubmodule) (N : Subgroup Source) [N.Normal] :
    ∃ i : Fin {n}, ∃ j : Fin {q}, states i=W ∧
      (BinaryTopRegistry{sid:03d}.states j).kernel=N ∧
      ((BinaryTopRegistry{sid:03d}.states j).degree+cost i<16 ∨
        exceptionalAxis i ∧ N=⊥) := by
  obtain ⟨i,hi⟩ := BinaryKernelAxes{mid:03d}.complete W hW
  obtain ⟨j,hj⟩ := BinaryTopRegistry{sid:03d}.complete N
  exact ⟨i,j,hi,hj,by simpa only [hj] using gap_or_trivial_top i j⟩
end SymmetricSubgroupAsymptotics.BinaryKernelGaps{mid:03d}
'''

def emit_central(t,m):
 entries=central_data(t,m,faithful_only=False)
 if not entries:return ''
 mid=m['id'];sid=t['id'];w=m['width'];ng=len(t['generators'])
 s=f'''
namespace SymmetricSubgroupAsymptotics.BinaryKernelCentral{mid:03d}
open BinaryKernelAxes{mid:03d}
local instance : Group Source := BinaryTopSource{sid:03d}.group
'''
 for ai,di,z in entries:
  one=dict(m,cuts=[ai],fixed=[di]);rows=fixed_factors(t,one)[0]
  terms=['['+','.join(f'({j},{l})' for j,l in row)+']' for row in rows]
  faithful_proof=f'''
/-- Checked faithfulness of the actual top action on K/A. -/
theorem faithful : ∀ g : Source,
    (∀ j,action g (kernelChart.inclusion (Pi.single j 1))-
      kernelChart.inclusion (Pi.single j 1)∈(charts {ai}).2.space) → g=1 := by
  simp only [action_numeric]
  decide +kernel
''' if (ai,di,z) in central_data(t,m) else ''
  s+=f'''
namespace Axis{ai}
private def factorEntries (l : Fin {w}) : List (Fin {ng} × Fin {w}) :=
  {lookup(terms,'l.val')}
private def factor : (Fin {ng} → Fin {w} → ZMod 2) →ₗ[ZMod 2] (Fin {w} → ZMod 2) :=
  LinearMap.pi (fun l => ((factorEntries l).map
    (fun p => (LinearMap.proj p.2).comp (LinearMap.proj p.1))).sum)
private theorem fixed_le_kernel_basis : ∀ j,
    (charts {di}).2.inclusion (Pi.single j 1)∈kernelChart.space := by decide +kernel
private theorem fixed_basis : ∀ j l,
    action (generators l) ((charts {di}).2.inclusion (Pi.single j 1))-
      (charts {di}).2.inclusion (Pi.single j 1)∈(charts {ai}).2.space := by
  simp only [action_numeric]
  decide +kernel
private theorem factor_basis : ∀ j,
    (charts {di}).2.defect (kernelChart.inclusion (Pi.single j 1))=
      factor (binaryCoordinate_generatorDefects action generators (charts {ai}).2
        (kernelChart.inclusion (Pi.single j 1))) := by
  simp only [binaryCoordinate_generatorDefects_apply,action_numeric]
  decide +kernel
private theorem full_fixed : ∀ v : Fin {w} → ZMod 2,
    v∈(charts {di}).2.space ↔ v∈kernelChart.space ∧
      ∀ j,action (generators j) v-v∈(charts {ai}).2.space :=
  binaryCoordinate_fixed_of_factor kernelChart (charts {ai}).2 (charts {di}).2
    action generators factor fixed_le_kernel_basis fixed_basis factor_basis

/-- The full fixed preimage of the exceptional axis itself. -/
theorem certificate : BinaryCoordinateCutData action kernel (states {ai}) (states {ai}) (states {di}) :=
  binaryCoordinate_cut_of_checks kernelChart (charts {ai}).2 (charts {ai}).2 (charts {di}).2
    action kernel (states {ai}) (states {ai}) (states {di}) rfl
    (states_space {ai}) (states_space {ai}) (states_space {di}) generators generators_full
    (by decide +kernel) (by decide +kernel)
    (by simp only [action_numeric]; decide +kernel) full_fixed

{faithful_proof}

theorem dimension : Module.finrank (ZMod 2) (states {di}).toSubmodule-
    Module.finrank (ZMod 2) (states {ai}).toSubmodule={z} := by
  rw [states_space {di},states_space {ai},(charts {di}).2.finrank,(charts {ai}).2.finrank]
  decide +kernel
end Axis{ai}
'''
 return s+f'end SymmetricSubgroupAsymptotics.BinaryKernelCentral{mid:03d}\n'

def main():
 ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--check',action='store_true');ap.add_argument('--batch',type=int,action='append')
 ap.add_argument('--pilot-module',type=int,help='Emit GapsPilotNNN for a single previously emitted axis/cut pilot.')
 a=ap.parse_args()
 if a.pilot_module is not None and a.batch is not None:ap.error('--pilot-module cannot be combined with --batch')
 ms=json.loads((OUT/'index.json').read_text());ts=json.loads((ROOT/'formal/SymmetricSubgroupAsymptotics/GeneratedTopNormals/index.json').read_text());batches={}
 for m in ms:
  if m['width']==8 and (a.pilot_module is None or m['id']==a.pilot_module):
   batches.setdefault(f'Pilot{m["id"]:03d}' if a.pilot_module is not None else m['batch'],[]).append(m)
 if a.pilot_module is not None and not batches:ap.error('Unknown width-sixteen pilot module')
 for batch,mods in batches.items():
  if a.batch is not None and int(batch[5:]) not in a.batch:continue
  s=f'import SymmetricSubgroupAsymptotics.GeneratedKernelAxes.Cuts{batch}\n\nset_option autoImplicit false\nset_option maxHeartbeats 0\nset_option maxRecDepth 100000\nnoncomputable section\n'
  s+='\n'.join(emit(ts[m['top_id']],m)+emit_central(ts[m['top_id']],m) for m in mods);p=OUT/f'Gaps{batch}.lean';b=s.encode()
  if a.check:
   if not p.exists() or p.read_bytes()!=b:raise SystemExit(f'Stale generated gap file {p}')
  elif not p.exists() or p.read_bytes()!=b:p.write_bytes(b)
  print(p.relative_to(ROOT),flush=True)
if __name__=='__main__':main()
