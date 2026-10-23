import SymmetricSubgroupAsymptotics.CFSGReeGTwoFixedTorusRegularity
import SymmetricSubgroupAsymptotics.CFSGFiniteFixedPointFreeCommutator
import Mathlib.GroupTheory.Subgroup.Centralizer

/-! The actual positive Ree 3-group lies in the derived subgroup of the
literal original fixed group. A regular torus element and finite Lang
surjectivity prove this without a Sylow or group-order formula. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGReeGTwoPositiveDerived
open CFSG.Models.Chevalley CFSGReeGTwoFieldParameters
open CFSGReeGTwoOriginalTorus CFSGReeGTwoFixedTorusAction
open CFSGReeGTwoFixedTorusRegularity CFSGReeGTwoOriginalPositiveSubgroup
open CFSGReeGTwoOriginalFixedWordChart CFSGReeGTwoFixedModelEquivalence

private theorem torus_conj_mem (m : ℕ) (t : (Field m)ˣ)
    (u : originalModelFixed m) (hu : u∈fixedPositiveGroup m) :
    fixedTorusHom m t*u*(fixedTorusHom m t)⁻¹ ∈ fixedPositiveGroup m := by
  obtain ⟨y,hy⟩ := fixedPositiveChart_surjective m (⟨u,hu⟩ : fixedPositiveGroup m)
  have he : fixedWord m y=u := congrArg (fun z : fixedPositiveGroup m => z.val) hy
  rw [←he,fixedTorus_fixedWord]
  exact (fixedPositiveChart m (fixedScaleCoordinates m t y)).property

theorem fixedTorus_mem_normalizer (m : ℕ) (t : (Field m)ˣ) :
    fixedTorusHom m t ∈ Subgroup.normalizer
      (fixedPositiveGroup m : Set (originalModelFixed m)) := by
  apply Subgroup.mem_normalizer_iff.mpr
  intro u
  constructor
  · exact torus_conj_mem m t u
  · intro hu
    have hv := torus_conj_mem m t⁻¹
      (fixedTorusHom m t*u*(fixedTorusHom m t)⁻¹) hu
    simpa only [map_inv, inv_inv, mul_assoc, inv_mul_cancel_left,
      inv_mul_cancel, mul_one] using hv

def fixedPositiveTorusAut (m : ℕ) (t : (Field m)ˣ) : MulAut (fixedPositiveGroup m) :=
  (fixedPositiveGroup m).normalizerMonoidHom ⟨fixedTorusHom m t,fixedTorus_mem_normalizer m t⟩

theorem fixedPositiveTorusAut_val (m : ℕ) (t : (Field m)ˣ)
    (u : fixedPositiveGroup m) :
    (fixedPositiveTorusAut m t u).val =
      fixedTorusHom m t*u.val*(fixedTorusHom m t)⁻¹ := rfl

theorem fixedPositiveGroup_le_commutator (m : ℕ) (hm : 1≤m) :
    fixedPositiveGroup m ≤ commutator (originalModelFixed m) := by
  letI : Finite (fixedPositiveGroup m) :=
    Finite.of_equiv (Fin 3 → Field m) (fixedPositiveEquiv m)
  obtain ⟨t,ht,htn⟩ := exists_regular_unit m hm
  apply CFSGFiniteFixedPointFreeCommutator.subgroup_le_commutator
    (fixedPositiveGroup m) (fixedTorusHom m t) (fixedPositiveTorusAut m t)
    (fixedPositiveTorusAut_val m t)
  intro u hu
  apply fixedTorus_centralizer_positive m t ht htn u
  exact (fixedPositiveTorusAut_val m t u).symm.trans
    (congrArg (fun z : fixedPositiveGroup m => z.val) hu)

theorem originalPositiveGroup_le_commutator (m : ℕ) (hm : 1≤m) :
    originalPositiveGroup m ≤ commutator
      (fixedSubgroup CartanMatrix.G₂ (Field m) CFSG.Models.reverseNode (originalExponent m)) := by
  rintro u ⟨v,hv,rfl⟩
  exact (CFSGSerreFixedModelEquivalence.derivedEquiv (originalFixedEquiv m).symm
    ⟨v,fixedPositiveGroup_le_commutator m hm hv⟩).property

end SymmetricSubgroupAsymptotics.CFSGReeGTwoPositiveDerived
