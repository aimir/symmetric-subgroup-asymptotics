import SymmetricSubgroupAsymptotics.CFSGReeFFourFixedOppositeGeneration
import SymmetricSubgroupAsymptotics.CFSGReeFFourFixedPositiveSylow
import SymmetricSubgroupAsymptotics.CFSGReeFFourOriginalPositiveSylow
import SymmetricSubgroupAsymptotics.CFSGGoodSylowPrimeSurjective

/-! Actual good-Sylow data for the full exceptional-fixed group, all m.
Transport to the original derived-center quotient is conditional here
on the literal full positive subgroup lying in the derived subgroup.
This remaining condition is stated explicitly, including at m=0. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourFixedGoodSylow
open CFSGReeFFourFixedModelEquivalence CFSGReeFFourFixedPositiveFamilies
open CFSGReeFFourOppositionFixedPositiveNegative CFSGReeFFourFixedPositiveSylow
open CFSGReeFFourFixedOppositeGeneration CFSGReeFFourFixedAmbientHom
open CFSGReeFFourOriginalPositiveSylow CFSGReduction
local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

private instance fixed_finite (m : ℕ) : Finite (originalModelFixed m) :=
  Finite.of_injective (fixedAmbientHom m) (fixedAmbientHom_injective m)

theorem fixed_goodSylowPrime (m : ℕ) : GoodSylowPrime (originalModelFixed m) 2 := by
  refine ⟨Nat.prime_two,fixedPositiveSylow m,oppositionFixed m,?_,?_⟩
  · simpa only [fixedPositiveSylow_coe] using fixed_positive_normalizer_soluble m
  · change Subgroup.closure
      (((fixedPositiveSylow m : Subgroup (originalModelFixed m)) : Set (originalModelFixed m)) ∪
        (fixedPositiveSylow m : Subgroup (originalModelFixed m)).map
          (MulAut.conj (oppositionFixed m)).toMonoidHom) = ⊤
    rw [fixedPositiveSylow_coe,fixed_positive_image_eq_fixed_negative,
      ← Subgroup.sup_eq_closure]
    exact fixed_positive_sup_negative m

theorem commutator_eq_top_of_positive_le (m : ℕ)
    (hU : fixedPositive m ≤ commutator (originalModelFixed m)) :
    commutator (originalModelFixed m) = ⊤ := by
  have hV : fixedNegative m ≤ commutator (originalModelFixed m) := by
    rw [← fixed_positive_image_eq_fixed_negative]
    rintro _ ⟨u,hu,rfl⟩
    exact (inferInstance : (commutator (originalModelFixed m)).Normal).conj_mem
      u (hU hu) (oppositionFixed m)
  apply top_unique
  rw [← fixed_positive_sup_negative m]
  exact sup_le hU hV

theorem original_goodSylowPrime_of_positive_le (m : ℕ)
    (hU : fixedPositive m ≤ commutator (originalModelFixed m)) :
    GoodSylowPrime (CFSG.Models.ReeF4 m) 2 := by
  have hperfect := commutator_eq_top_of_positive_le m hU
  let e : commutator (originalModelFixed m) ≃* originalModelFixed m :=
    (MulEquiv.subgroupCongr hperfect).trans (Subgroup.topEquiv)
  let f := (derivedReeHom m).comp e.symm.toMonoidHom
  have hf : Function.Surjective f := (derivedReeHom_surjective m).comp e.symm.surjective
  exact goodSylowPrime_surjective f hf (fixed_goodSylowPrime m)

end SymmetricSubgroupAsymptotics.CFSGReeFFourFixedGoodSylow
