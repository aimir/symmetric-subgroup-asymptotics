import SymmetricSubgroupAsymptotics.CFSGGTwoGoodSylow
import SymmetricSubgroupAsymptotics.CFSGGTwoModelEvenOrder
import SymmetricSubgroupAsymptotics.CFSGGoodSylowPrimeSurjective

/-! The actual natural G2 GoodSylow witness descends through the SAME
nontrivial action-image central quotient to the original simple Serre
projective model. No faithfulness of the natural representation is used. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGGTwoOriginalGoodSylow
open CFSGGTwoSerreMatrices CFSG.Models.Chevalley

theorem original_goodSylowPrime (K : Type) [Field K] [Finite K]
    (p : ℕ) [Fact p.Prime] [CharP K p] [IsSimpleGroup (Projective CartanMatrix.G₂ K)] :
    CFSGReduction.GoodSylowPrime (Projective CartanMatrix.G₂ K) p := by
  letI : Fintype K := Fintype.ofFinite K
  let H := naturalActionImage K
  let q := QuotientGroup.mk' (Subgroup.center H)
  have hne : q (imageLongWeyl K) ≠ 1 := by
    intro h
    exact imageLongWeyl_not_center K ((QuotientGroup.eq_one_iff _).mp h)
  letI : Nontrivial (H ⧸ Subgroup.center H) := ⟨⟨q (imageLongWeyl K), 1, hne⟩⟩
  let e := CFSGSimpleProjectiveDescent.projectiveEquivOfSimple
    (modelToNaturalImage K) (modelToNaturalImage_surjective K)
  let a := (naturalImageAction K).rangeRestrict
  let f := e.symm.toMonoidHom.comp (q.comp a)
  have hf : Function.Surjective f := e.symm.surjective.comp
    ((QuotientGroup.mk'_surjective (Subgroup.center H)).comp
      (naturalImageAction K).rangeRestrict_surjective)
  exact CFSGReduction.goodSylowPrime_surjective f hf
    (CFSGGTwoGoodSylow.natural_goodSylowPrime K p)

theorem typeGTwo_goodSylowPrime (q : CFSG.PrimePower) [IsSimpleGroup (CFSG.Models.G2 q)] :
    CFSGReduction.GoodSylowPrime (CFSG.Models.G2 q) q.prime :=
  original_goodSylowPrime q.Field q.prime

end SymmetricSubgroupAsymptotics.CFSGGTwoOriginalGoodSylow
