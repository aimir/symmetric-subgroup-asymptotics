import SymmetricSubgroupAsymptotics.BinaryPlaneAlternatingNormalRegularHom
import Mathlib.Data.Fintype.Perm

/-! Faithfulness of the actual top makes its regular Klein lifts unique.
The resulting homomorphism is normal in the actual linear image, without
assuming an affine splitting or a trivial kernel before proving it. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.BinaryPlaneFaithfulTopRegularLift
open BinaryPlaneAlternatingKernelPartition (Frame)
open BinaryPlaneAlternatingCentralizerCommutators (R regular top regular_injective)
local instance : Fintype R := BinaryRegularKleinWreath.rFintype
local instance : DecidableEq R := BinaryRegularKleinWreath.rDecidableEq

private theorem regular_even : ∀ r : R, regular r∈alternatingGroup (Fin 4) := by
  change ∀ r : R, Equiv.Perm.sign (regular r)=1
  decide +kernel

private theorem conjugate_regular : ∀ (p : Equiv.Perm (Fin 4)) (r : R),
    ∃ s : R, p*regular r*p⁻¹=regular s := by decide +kernel

/-- The genuine regular subgroup supplied to the gauge. -/
theorem exists_lift (C : Subgroup Frame) (hinj : Function.Injective (top C))
    (heven : ∀ p : alternatingGroup (Fin 4), ∃ h : C, (h : Frame).right=p.val) :
    ∃ l : R →* C, Function.Injective l ∧ l.range.Normal ∧
      ∀ r, top C (l r)=regular r := by
  have hex : ∀ r : R, ∃ h : C, top C h=regular r := by
    intro r
    exact heven ⟨regular r,regular_even r⟩
  choose f hf using hex
  let l : R →* C := {
    toFun := f
    map_one' := hinj (by simpa only [map_one] using hf (1 : R))
    map_mul' := fun r s => hinj (by
      calc
        top C (f (r*s)) = regular (r*s) := hf _
        _ = regular r*regular s := regular.map_mul r s
        _ = top C (f r*f s) := by rw [map_mul,hf,hf]) }
  have ht : ∀ r, top C (l r)=regular r := hf
  refine ⟨l,?_,?_,ht⟩
  · intro r s h
    apply regular_injective
    exact (ht r).symm.trans ((congrArg (top C) h).trans (ht s))
  · constructor
    intro x hx g
    obtain ⟨r,rfl⟩ := hx
    obtain ⟨s,hs⟩ := conjugate_regular (top C g) r
    refine ⟨s,hinj ?_⟩
    rw [map_mul,map_mul,map_inv,ht,ht]
    exact hs.symm

end SymmetricSubgroupAsymptotics.BinaryPlaneFaithfulTopRegularLift
