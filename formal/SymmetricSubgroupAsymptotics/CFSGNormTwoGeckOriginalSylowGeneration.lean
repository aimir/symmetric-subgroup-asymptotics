import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckSylowGeneration
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckModelEvenOrder
import SymmetricSubgroupAsymptotics.CFSGGoodSylowPrimeSurjective

/-! Actual two-conjugate-Sylow generation of the ORIGINAL simple
projective Serre model. The source/image comparison is only through its
actual nontrivial central quotient, not Lie or group faithfulness. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoGeckOriginalSylowGeneration
open CFSG.Models.Chevalley CFSGIntegerMatrixPairing CFSGNormTwoRootPairing
open CFSGGeckSerreRepresentation CFSGNormTwoGeckIntegralRealization CFSGNormTwoGeckHeightData
open CFSGNormTwoGeckImageWeylWitness CFSGNormTwoGeckModelEvenOrder
variable {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℤ) (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    [Fintype (Roots A)] [DecidableEq (Roots A)] [(rootPairing A hs hp).IsIrreducible]
    (b : (rootPairing A hs hp).Base) {r : ℕ} (s : Fin r≃b.support)
    (hsimple : ∀j : b.support,rootSign A j= -1)
    (height : (n→ℤ)→ₗ[ℤ]ℤ) (hheight : ∀j : b.support,height (j:Roots A).val=1)
    (K : Type) [Field K] [Finite K] (p : ℕ) [Fact p.Prime] [CharP K p]

include hsimple height hheight

theorem original_two_conjugate_sylows [IsSimpleGroup (Projective (cartan b s) K)] (i : Fin r) :
    ∃(P : Sylow p (Projective (cartan b s) K)) (g : Projective (cartan b s) K),
      Subgroup.closure ((P : Set (Projective (cartan b s) K)) ∪
        (P : Subgroup (Projective (cartan b s) K)).map (MulAut.conj g).toMonoidHom)=⊤ := by
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
  obtain ⟨P,g,hg⟩ := CFSGNormTwoGeckSylowGeneration.canonical_two_conjugate_sylows
    A hs hp b s height hheight K p
  let Q : Sylow p (Projective (cartan b s) K) := P.mapSurjective (f:=f) hf
  refine ⟨Q,f g,?_⟩
  exact CFSGReduction.two_conjugates_generate_surjective f hf (P : Subgroup
    (CFSGSerreQuadraticMatrix.canonicalElementaryGroup (realizationData A hs hp b s) K)) g hg

theorem original_two_conjugate_sylows_of_cartan_eq {C : Matrix (Fin r) (Fin r) ℤ}
    (hC : cartan b s=C) [IsSimpleGroup (Projective C K)] (i : Fin r) :
    ∃(P : Sylow p (Projective C K)) (g : Projective C K),
      Subgroup.closure ((P : Set (Projective C K)) ∪
        (P : Subgroup (Projective C K)).map (MulAut.conj g).toMonoidHom)=⊤ := by
  subst C
  exact original_two_conjugate_sylows A hs hp b s hsimple height hheight K p i

end SymmetricSubgroupAsymptotics.CFSGNormTwoGeckOriginalSylowGeneration
