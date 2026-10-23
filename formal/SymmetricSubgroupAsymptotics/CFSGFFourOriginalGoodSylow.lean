import SymmetricSubgroupAsymptotics.CFSGFFourE6GoodSylow
import SymmetricSubgroupAsymptotics.CFSGFFourFullRootAction
import SymmetricSubgroupAsymptotics.CFSGFFourModelEvenOrder

/-! Good Sylow data for the ORIGINAL simple F4 Serre projective model.
The full literal folded group surjects onto its SAME original action
image. The established noncentral Weyl witness then permits simple
projective descent; no source faithfulness is asserted or needed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGFFourOriginalGoodSylow
open CFSGFFourSerreMatrices CFSGFFourE6GoodSylow
open CFSGSerreQuadraticMatrix CFSG.Models.Chevalley CFSGReduction

def foldedToImage (K : Type) [Field K] :
    canonicalElementaryGroup realizationData K→*imageGroup K :=
  (fullNaturalImageAction K).codRestrict _ (fun g=>by
    change fullNaturalImageAction K g∈(imageRepresentation realizationData K).range
    rw [full_action_ranges_eq]
    exact ⟨g,rfl⟩)

theorem foldedToImage_surjective (K : Type) [Field K] : Function.Surjective (foldedToImage K) := by
  intro y
  have hy : y.val∈(fullNaturalImageAction K).range := by
    rw [←full_action_ranges_eq]
    exact y.property
  obtain ⟨g,hg⟩ := hy
  exact ⟨g,Subtype.ext hg⟩

theorem image_goodSylowPrime (K : Type) [Field K] [Finite K]
    (p : ℕ) [Fact p.Prime] [CharP K p] : GoodSylowPrime (imageGroup K) p :=
  goodSylowPrime_surjective (foldedToImage K) (foldedToImage_surjective K)
    (folded_goodSylowPrime K p)

theorem serreTypeFFour_goodSylowPrime (K : Type) [Field K] [Finite K]
    (p : ℕ) [Fact p.Prime] [CharP K p] [IsSimpleGroup (Projective CartanMatrix.F₄ K)] :
    GoodSylowPrime (Projective CartanMatrix.F₄ K) p := by
  let H := imageGroup K
  letI : Finite H := Finite.of_surjective (foldedToImage K) (foldedToImage_surjective K)
  let q := QuotientGroup.mk' (Subgroup.center H)
  have hne : q (imageWeyl K)≠1 := by
    intro h
    exact imageWeyl_not_center K ((QuotientGroup.eq_one_iff _).mp h)
  letI : Nontrivial (H⧸Subgroup.center H) := ⟨⟨q (imageWeyl K),1,hne⟩⟩
  let e := CFSGSimpleProjectiveDescent.projectiveEquivOfSimple
    (imageRepresentation realizationData K).rangeRestrict
    (imageRepresentation realizationData K).rangeRestrict_surjective
  let f := e.symm.toMonoidHom.comp q
  have hf : Function.Surjective f :=
    e.symm.surjective.comp (QuotientGroup.mk'_surjective (Subgroup.center H))
  exact goodSylowPrime_surjective f hf (image_goodSylowPrime K p)

theorem typeFFour_goodSylowPrime (q : CFSG.PrimePower) [IsSimpleGroup (CFSG.Models.F4 q)] :
    GoodSylowPrime (CFSG.Models.F4 q) q.prime := by
  letI : Fact q.prime.Prime := ⟨q.prime_isPrime⟩
  exact serreTypeFFour_goodSylowPrime q.Field q.prime

end SymmetricSubgroupAsymptotics.CFSGFFourOriginalGoodSylow
