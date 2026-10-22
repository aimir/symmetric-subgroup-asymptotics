import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckImageWeylWitness
import SymmetricSubgroupAsymptotics.CFSGSimpleProjectiveDescent

/-! Simplicity of the ORIGINAL projective Serre model identifies it with
its nontrivial actual image modulo centre. No Lie injectivity or named
finite-group recognition is assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoGeckModelEvenOrder
open CFSG.Models.Chevalley CFSGIntegerMatrixPairing CFSGNormTwoRootPairing
open CFSGGeckSerreRepresentation CFSGNormTwoGeckIntegralRealization CFSGNormTwoGeckHeightData
open CFSGNormTwoGeckImageWeylWitness CFSGSerreQuadraticMatrix
variable {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℤ) (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    [Fintype (Roots A)] [DecidableEq (Roots A)] [(rootPairing A hs hp).IsIrreducible]
    (b : (rootPairing A hs hp).Base) {r : ℕ} (s : Fin r≃b.support)
    (hsimple : ∀ j : b.support,rootSign A j= -1) (K : Type) [Field K]
include hsimple

theorem original_action_ranges_eq :
    (imageRepresentation (realizationData A hs hp b s) K).range=
      (imageAction A hs hp b s hsimple K).range :=
  canonical_action_ranges_eq (realizationData A hs hp b s) K
    (CFSGNormTwoGeckImageFourthCoefficient.baseChange_image_fourth_coefficient_zero
      A hs hp b s hsimple K)

def originalToImage : Model (cartan b s) K→*imageGroup A hs hp b s hsimple K where
  toFun g := ⟨imageRepresentation (realizationData A hs hp b s) K g,by
    change imageRepresentation (realizationData A hs hp b s) K g∈
      (imageAction A hs hp b s hsimple K).range
    rw [←original_action_ranges_eq A hs hp b s hsimple K]
    exact ⟨g,rfl⟩⟩
  map_one' := Subtype.ext (map_one (imageRepresentation (realizationData A hs hp b s) K))
  map_mul' g h := Subtype.ext (map_mul (imageRepresentation (realizationData A hs hp b s) K) g h)

theorem originalToImage_surjective : Function.Surjective (originalToImage A hs hp b s hsimple K) := by
  rintro ⟨g,hg⟩
  have h : g∈(imageRepresentation (realizationData A hs hp b s) K).range := by
    rw [original_action_ranges_eq A hs hp b s hsimple K]
    exact hg
  obtain ⟨x,hx⟩ := h
  exact ⟨x,Subtype.ext hx⟩

theorem original_even_card [IsSimpleGroup (Projective (cartan b s) K)] (i : Fin r) :
    Even (Nat.card (Projective (cartan b s) K)) := by
  let H := imageGroup A hs hp b s hsimple K
  let q := QuotientGroup.mk' (Subgroup.center H)
  have hne : q (imageWeyl A hs hp b s hsimple K i)≠1 := by
    intro h
    exact imageWeyl_not_center A hs hp b s hsimple K i ((QuotientGroup.eq_one_iff _).mp h)
  letI : Nontrivial (H⧸Subgroup.center H) :=
    ⟨⟨q (imageWeyl A hs hp b s hsimple K i),1,hne⟩⟩
  let e := CFSGSimpleProjectiveDescent.projectiveEquivOfSimple
    (originalToImage A hs hp b s hsimple K) (originalToImage_surjective A hs hp b s hsimple K)
  change Even (Nat.card (Model (cartan b s) K⧸Subgroup.center (Model (cartan b s) K)))
  rw [Nat.card_congr e.toEquiv]
  exact imageProjective_even_card A hs hp b s hsimple K i

theorem original_even_card_of_cartan_eq {C : Matrix (Fin r) (Fin r) ℤ}
    (hC : cartan b s=C) [IsSimpleGroup (Projective C K)] (i : Fin r) :
    Even (Nat.card (Projective C K)) := by
  subst C
  exact original_even_card A hs hp b s hsimple K i

end SymmetricSubgroupAsymptotics.CFSGNormTwoGeckModelEvenOrder
