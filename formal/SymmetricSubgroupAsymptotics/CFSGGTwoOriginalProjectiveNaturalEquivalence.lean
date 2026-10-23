import SymmetricSubgroupAsymptotics.CFSGGTwoOriginalNaturalEquivalence
import SymmetricSubgroupAsymptotics.CFSGGTwoNaturalCenter
import Mathlib.GroupTheory.QuotientGroup.Basic

/-! The original projective G2 quotient has an exact native model for
fields with at least three elements, independently of ordinary G2
simplicity. This bridge is therefore available for original exceptional
fixed-subgroup presentations over characteristic-three fields. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGGTwoOriginalProjectiveNaturalEquivalence
open CFSG.Models.Chevalley CFSGGTwoSerreMatrices
open CFSGGTwoOriginalNaturalEquivalence
variable (K : Type) [Field K]

theorem model_center_eq_bot_of_parameter (c : K) (hc0 : c≠0) (hc1 : c≠1) :
    Subgroup.center (Model CartanMatrix.G₂ K)=⊥ := by
  apply (Subgroup.eq_bot_iff_forall _).mpr
  intro g hg
  have hc : modelEquivNatural K g∈Subgroup.center (naturalGroup K) := by
    apply Subgroup.mem_center_iff.mpr
    intro h
    obtain ⟨k,rfl⟩ := (modelEquivNatural K).surjective h
    simpa only [←map_mul] using
      congrArg (modelEquivNatural K) ((Subgroup.mem_center_iff.mp hg) k)
  rw [CFSGGTwoNaturalCenter.center_eq_bot_of_parameter K c hc0 hc1] at hc
  apply (modelEquivNatural K).injective
  simpa only [map_one] using Subgroup.mem_bot.mp hc

theorem model_center_eq_bot [Finite K] (hcard : 3≤Nat.card K) :
    Subgroup.center (Model CartanMatrix.G₂ K)=⊥ := by
  apply (Subgroup.eq_bot_iff_forall _).mpr
  intro g hg
  have hc : modelEquivNatural K g∈Subgroup.center (naturalGroup K) := by
    apply Subgroup.mem_center_iff.mpr
    intro h
    obtain ⟨k,rfl⟩ := (modelEquivNatural K).surjective h
    simpa only [←map_mul] using
      congrArg (modelEquivNatural K) ((Subgroup.mem_center_iff.mp hg) k)
  rw [CFSGGTwoNaturalCenter.center_eq_bot K hcard] at hc
  apply (modelEquivNatural K).injective
  simpa only [map_one] using Subgroup.mem_bot.mp hc

def projectiveEquivNatural [Finite K] (hcard : 3≤Nat.card K) :
    Projective CartanMatrix.G₂ K ≃* naturalGroup K :=
  (QuotientGroup.quotientMulEquivOfEq (model_center_eq_bot K hcard)).trans
    (QuotientGroup.quotientBot.trans (modelEquivNatural K))

end SymmetricSubgroupAsymptotics.CFSGGTwoOriginalProjectiveNaturalEquivalence
