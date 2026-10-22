import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckOriginalSylowGeneration

/-! Actual good Sylow data descends from the canonical matrix group onto
the ORIGINAL simple projective Serre model, through the established actual
image and its nontrivial central quotient. No source faithfulness occurs. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoGeckOriginalGoodSylow
open CFSG.Models.Chevalley CFSGIntegerMatrixPairing CFSGNormTwoRootPairing
open CFSGGeckSerreRepresentation CFSGNormTwoGeckIntegralRealization CFSGNormTwoGeckHeightData
open CFSGNormTwoGeckImageWeylWitness CFSGNormTwoGeckModelEvenOrder
variable {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℤ) (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    [Fintype (Roots A)] [DecidableEq (Roots A)] [(rootPairing A hs hp).IsIrreducible]
    (b : (rootPairing A hs hp).Base) {r : ℕ} (s : Fin r≃b.support)
    (hsimple : ∀j : b.support,rootSign A j= -1)
    (K : Type) [Field K] [Finite K] (p : ℕ)
include hsimple

theorem original_goodSylow [IsSimpleGroup (Projective (cartan b s) K)]
    (hgood : CFSGReduction.GoodSylowPrime
      (CFSGSerreQuadraticMatrix.canonicalElementaryGroup (realizationData A hs hp b s) K) p)
    (i : Fin r) : CFSGReduction.GoodSylowPrime (Projective (cartan b s) K) p := by
  letI : Fintype K := Fintype.ofFinite K
  let H := imageGroup A hs hp b s hsimple K
  let q := QuotientGroup.mk' (Subgroup.center H)
  have hne : q (imageWeyl A hs hp b s hsimple K i)≠1 := by
    intro h
    exact imageWeyl_not_center A hs hp b s hsimple K i ((QuotientGroup.eq_one_iff _).mp h)
  letI : Nontrivial (H⧸Subgroup.center H) :=
    ⟨⟨q (imageWeyl A hs hp b s hsimple K i),1,hne⟩⟩
  let e := CFSGSimpleProjectiveDescent.projectiveEquivOfSimple
    (originalToImage A hs hp b s hsimple K) (originalToImage_surjective A hs hp b s hsimple K)
  let a := (imageAction A hs hp b s hsimple K).rangeRestrict
  let f := e.symm.toMonoidHom.comp (q.comp a)
  have hf : Function.Surjective f := e.symm.surjective.comp
    ((QuotientGroup.mk'_surjective (Subgroup.center H)).comp
      (imageAction A hs hp b s hsimple K).rangeRestrict_surjective)
  exact CFSGReduction.goodSylowPrime_surjective f hf hgood

theorem original_goodSylow_of_cartan_eq {C : Matrix (Fin r) (Fin r) ℤ}
    (hC : cartan b s=C) [IsSimpleGroup (Projective C K)]
    (hgood : CFSGReduction.GoodSylowPrime
      (CFSGSerreQuadraticMatrix.canonicalElementaryGroup (realizationData A hs hp b s) K) p)
    (i : Fin r) : CFSGReduction.GoodSylowPrime (Projective C K) p := by
  subst C
  exact original_goodSylow A hs hp b s hsimple K p hgood i

end SymmetricSubgroupAsymptotics.CFSGNormTwoGeckOriginalGoodSylow
