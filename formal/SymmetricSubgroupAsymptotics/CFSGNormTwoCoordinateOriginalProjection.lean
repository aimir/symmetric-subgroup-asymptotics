import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinatePositiveQuotientInjectivity
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckOriginalGoodSylow

/-! The ACTUAL surjection from canonical matrices to the ORIGINAL simple
projective Serre model, and its proved-candidate restriction injectivity
on U. The coordinate root signs are discharged internally. No source
faithfulness, named-group identification, or kernel premise is supplied. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateOriginalProjection
open CFSG.Models.Chevalley CFSGIntegerMatrixPairing CFSGNormTwoRootPairing
open CFSGGeckSerreRepresentation CFSGNormTwoGeckIntegralRealization CFSGNormTwoGeckHeightData
open CFSGNormTwoGeckImageWeylWitness CFSGNormTwoGeckModelEvenOrder
open CFSGNormTwoCoordinateElementaryRootParameters CFSGNormTwoCoordinatePositiveQuotientInjectivity
variable {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ) (hd : ∀i,A i i=2)
    (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    (ho : ∀i j,i≠j→A i j≤0)
    [Fintype (Roots A)] [DecidableEq (Roots A)]
    [(rootPairing A hs hp).IsReduced] [(rootPairing A hs hp).IsIrreducible]
    (K : Type) [Field K]
local notation "b₀" => coordinateBase A hd hs hp ho
local notation "s₀" => coordinateIndexEquiv A hd hs hp ho
private abbrev ActualImage := imageGroup A hs hp b₀ s₀ (rootSign_simple A hd hs hp ho) K

def originalImageProjectiveEquiv [IsSimpleGroup (Projective (cartan b₀ s₀) K)] (i : Fin r) :
    Projective (cartan b₀ s₀) K≃*ActualImage A hd hs hp ho K⧸Subgroup.center (ActualImage A hd hs hp ho K) := by
  let H := ActualImage A hd hs hp ho K
  let q := QuotientGroup.mk' (Subgroup.center H)
  have hne : q (imageWeyl A hs hp b₀ s₀ (rootSign_simple A hd hs hp ho) K i)≠1 := by
    intro h
    exact imageWeyl_not_center A hs hp b₀ s₀ (rootSign_simple A hd hs hp ho) K i
      ((QuotientGroup.eq_one_iff _).mp h)
  letI : Nontrivial (H⧸Subgroup.center H) :=
    ⟨⟨q (imageWeyl A hs hp b₀ s₀ (rootSign_simple A hd hs hp ho) K i),1,hne⟩⟩
  exact CFSGSimpleProjectiveDescent.projectiveEquivOfSimple
    (originalToImage A hs hp b₀ s₀ (rootSign_simple A hd hs hp ho) K)
    (originalToImage_surjective A hs hp b₀ s₀ (rootSign_simple A hd hs hp ho) K)

def originalProjection [IsSimpleGroup (Projective (cartan b₀ s₀) K)] (i : Fin r) :
    ElementaryGroup A hd hs hp ho K→*Projective (cartan b₀ s₀) K :=
  (originalImageProjectiveEquiv A hd hs hp ho K i).symm.toMonoidHom.comp
    ((QuotientGroup.mk' (Subgroup.center (ActualImage A hd hs hp ho K))).comp
      (imageAction A hs hp b₀ s₀ (rootSign_simple A hd hs hp ho) K).rangeRestrict)

theorem originalProjection_surjective [IsSimpleGroup (Projective (cartan b₀ s₀) K)] (i : Fin r) :
    Function.Surjective (originalProjection A hd hs hp ho K i) :=
  (originalImageProjectiveEquiv A hd hs hp ho K i).symm.surjective.comp
    ((QuotientGroup.mk'_surjective (Subgroup.center (ActualImage A hd hs hp ho K))).comp
      (imageAction A hs hp b₀ s₀ (rootSign_simple A hd hs hp ho) K).rangeRestrict_surjective)

theorem originalProjection_positive_injective [Finite K] [Nontrivial (Fin r)]
    (p : ℕ) [Fact p.Prime] [CharP K p]
    [IsSimpleGroup (Projective (cartan b₀ s₀) K)] (i : Fin r) :
    Function.Injective ((originalProjection A hd hs hp ho K i).comp
      (positiveInclusion A hd hs hp ho K)) :=
  positive_quotient_injective A hd hs hp ho K p
    (originalProjection A hd hs hp ho K i) (originalProjection_surjective A hd hs hp ho K i)

end SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateOriginalProjection
