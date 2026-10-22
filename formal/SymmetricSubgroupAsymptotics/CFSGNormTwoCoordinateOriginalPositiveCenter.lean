import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateOriginalProjection
import SymmetricSubgroupAsymptotics.CFSGInjectiveHomCenterImage
import SymmetricSubgroupAsymptotics.CFSGNormalizerCenterAtoms

/-! Literal positive subgroup and its FULL centre in the ORIGINAL simple
projective Serre model. The canonical U equivalence uses the proved
quotient restriction injectivity. Sylow recognition is a separate step. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateOriginalPositiveCenter
open CFSG.Models.Chevalley CFSGIntegerMatrixPairing CFSGNormTwoRootPairing
open CFSGGeckSerreRepresentation CFSGNormTwoCoordinateRootHeightQuotient
open CFSGNormTwoCoordinatePositiveQuotientInjectivity CFSGNormTwoCoordinateOriginalProjection
open CFSGNormTwoCoordinatePositiveCenter CFSGNormTwoCoordinateRootSubgroup
open CFSGNormalizerCenterAtoms CFSGInjectiveHomCenterImage
variable {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ) (hd : ∀i,A i i=2)
    (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    (ho : ∀i j,i≠j→A i j≤0)
    [Fintype (Roots A)] [DecidableEq (Roots A)]
    [(rootPairing A hs hp).IsReduced] [(rootPairing A hs hp).IsIrreducible]
    (K : Type) [Field K]
local notation "b₀" => coordinateBase A hd hs hp ho
local notation "s₀" => coordinateIndexEquiv A hd hs hp ho

def originalPositive [IsSimpleGroup (Projective (cartan b₀ s₀) K)] (i : Fin r) :
    Subgroup (Projective (cartan b₀ s₀) K) :=
  ((originalProjection A hd hs hp ho K i).comp (positiveInclusion A hd hs hp ho K)).range

def originalPositiveEquiv [Finite K] [Nontrivial (Fin r)]
    (p : ℕ) [Fact p.Prime] [CharP K p]
    [IsSimpleGroup (Projective (cartan b₀ s₀) K)] (i : Fin r) :
    PositiveGroup A hd hs hp ho K ≃* originalPositive A hd hs hp ho K i :=
  MonoidHom.ofInjective (originalProjection_positive_injective A hd hs hp ho K p i)

theorem original_positive_center_eq_dominant_image [Finite K] [Nontrivial (Fin r)]
    (p : ℕ) [Fact p.Prime] [CharP K p]
    [IsSimpleGroup (Projective (cartan b₀ s₀) K)] (i : Fin r) (θ : Roots A)
    (hθ : ∀j,0≤θ.val j)
    (hdom : ∀j,0 ≤ integerPairing A θ.val (Pi.single j (1:ℤ) : Fin r→ℤ)) :
    centerImage (originalPositive A hd hs hp ho K i)=
      ((rootSubgroup A hd hs hp ho K θ).subgroupOf (PositiveGroup A hd hs hp ho K)).map
        ((originalProjection A hd hs hp ho K i).comp (positiveInclusion A hd hs hp ho K)) := by
  rw [centerImage,originalPositive,
    center_range_image_eq _ (originalProjection_positive_injective A hd hs hp ho K p i),
    center_eq_dominant_root_subgroup A hd hs hp ho K θ hθ hdom]

end SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateOriginalPositiveCenter
