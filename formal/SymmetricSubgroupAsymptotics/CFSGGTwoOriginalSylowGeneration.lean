import SymmetricSubgroupAsymptotics.CFSGGTwoSylowGeneration
import SymmetricSubgroupAsymptotics.CFSGGTwoModelEvenOrder
import SymmetricSubgroupAsymptotics.CFSGGoodSylowPrimeSurjective

/-! The actual two-conjugate-Sylow conclusion descends to the ORIGINAL
simple projective G2 Serre model through its SAME nontrivial image central
quotient. No injectivity of the natural representation is assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGGTwoOriginalSylowGeneration
open CFSGGTwoSerreMatrices CFSG.Models.Chevalley

theorem original_two_conjugate_sylows (K : Type) [Field K] [Finite K]
    (p : ℕ) [Fact p.Prime] [CharP K p] [IsSimpleGroup (Projective CartanMatrix.G₂ K)] :
    ∃ (P : Sylow p (Projective CartanMatrix.G₂ K)) (g : Projective CartanMatrix.G₂ K),
      Subgroup.closure ((P : Set (Projective CartanMatrix.G₂ K)) ∪
        (P : Subgroup (Projective CartanMatrix.G₂ K)).map (MulAut.conj g).toMonoidHom) = ⊤ := by
  letI : Fintype K := Fintype.ofFinite K
  let H := naturalActionImage K
  let q := QuotientGroup.mk' (Subgroup.center H)
  have hne : q (imageLongWeyl K) ≠ 1 := by
    intro h
    exact imageLongWeyl_not_center K ((QuotientGroup.eq_one_iff _).mp h)
  letI : Nontrivial (H ⧸ Subgroup.center H) :=
    ⟨⟨q (imageLongWeyl K), 1, hne⟩⟩
  let e := CFSGSimpleProjectiveDescent.projectiveEquivOfSimple
    (modelToNaturalImage K) (modelToNaturalImage_surjective K)
  let a := (naturalImageAction K).rangeRestrict
  let f := e.symm.toMonoidHom.comp (q.comp a)
  have hf : Function.Surjective f := e.symm.surjective.comp
    ((QuotientGroup.mk'_surjective (Subgroup.center H)).comp
      (naturalImageAction K).rangeRestrict_surjective)
  obtain ⟨P, g, hg⟩ := CFSGGTwoSylowGeneration.natural_two_conjugate_sylows K p
  let Q : Sylow p (Projective CartanMatrix.G₂ K) := P.mapSurjective (f := f) hf
  refine ⟨Q, f g, ?_⟩
  exact CFSGReduction.two_conjugates_generate_surjective f hf
    (P : Subgroup (naturalGroup K)) g hg

theorem typeGTwo_two_conjugate_sylows (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.G2 q)] :
    ∃ (P : Sylow q.prime (CFSG.Models.G2 q)) (g : CFSG.Models.G2 q),
      Subgroup.closure ((P : Set (CFSG.Models.G2 q)) ∪
        (P : Subgroup (CFSG.Models.G2 q)).map (MulAut.conj g).toMonoidHom) = ⊤ :=
  original_two_conjugate_sylows q.Field q.prime

end SymmetricSubgroupAsymptotics.CFSGGTwoOriginalSylowGeneration
