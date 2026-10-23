import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateNormalizerEnvelope
import SymmetricSubgroupAsymptotics.CFSGGradedDiagonalOppositeIntersection
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckOppositeIntersection
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateHeight
import SymmetricSubgroupAsymptotics.CFSGCentralTwistedProductCoordinates

/-! The actual coordinate normalizer envelope meets the opposite
unipotent group trivially, has unique positive/diagonal factors, and
retains the entire actual elementary-group centre in its diagonal factor.
No scalar-centre, torus recognition, or fixed-point lifting is used. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateEnvelopeIntersection
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing
open CFSGSerreQuadraticMatrix
open CFSGNormTwoCoordinateNormalizerEnvelope CFSGGradedDiagonalOppositeIntersection
open CFSGNormTwoGeckOppositeIntersection CFSGNormTwoCoordinateHeight
open CFSGNormTwoGeckHeightSupport CFSGNormTwoGeckPositivePGroup
open CFSGNormTwoGeckIntegralRealization CFSGNormTwoGeckWeylWordDegree
open CFSGNormTwoGeckWeylLatticeLinear CFSGCentralTwistedProductCoordinates
variable {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ) (hd : ∀j,A j j=2)
    (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    (ho : ∀i j,i≠j→A i j≤0)
    [Fintype (Roots A)] [DecidableEq (Roots A)] [(rootPairing A hs hp).IsIrreducible]
local notation "b₀" => coordinateBase A hd hs hp ho
local notation "s₀" => coordinateIndexEquiv A hd hs hp ho
local notation "J₀" => CFSGNormTwoCoordinateWeylBlocks.GeckIndex A hd hs hp ho
local notation "D₀" => realizationData A hs hp b₀ s₀

theorem negative_le_elementary (K : Type) [Field K] :
    Negative A hd hs hp ho K ≤ Elementary A hd hs hp ho K := by
  change rootGroup A hs hp b₀ s₀ K true ≤ canonicalElementaryGroup D₀ K
  rw [←positive_sup_negative A hs hp b₀ s₀ K]
  exact le_sup_right

theorem center_mem_diagonalNormalizer (K : Type) [Field K]
    (z : Elementary A hd hs hp ho K) (hz : z ∈ Subgroup.center (Elementary A hd hs hp ho K)) :
    z.val ∈ diagonalNormalizer A hd hs hp ho K :=
  ⟨⟨center_normalizes_subgroup (Elementary A hd hs hp ho K) (Positive A hd hs hp ho K)
    (positive_le_elementary A hd hs hp ho K) z hz,
    center_normalizes_subgroup (Elementary A hd hs hp ho K) (Negative A hd hs hp ho K)
      (negative_le_elementary A hd hs hp ho K) z hz⟩,z.property⟩

theorem center_map_le_diagonalNormalizer (K : Type) [Field K] :
    (Subgroup.center (Elementary A hd hs hp ho K)).map
      (Elementary A hd hs hp ho K).subtype ≤ diagonalNormalizer A hd hs hp ho K := by
  rintro _ ⟨z,hz,rfl⟩
  exact center_mem_diagonalNormalizer A hd hs hp ho K z hz

variable (K : Type) [Field K]
    (ε : Fin r→ℤ) (hε : ∀i,ε i*ε i=1)
    (hA : ∀i j,ε i*|A i j|=A j i*ε j)
    (hidentity : ∀w : List (Fin r),wordUnit A hs hp
      (coordinateBase A hd hs hp ho) (coordinateIndexEquiv A hd hs hp ho) K w∈
      Subgroup.normalizer (Positive A hd hs hp ho K : Set _)→
      wordLinear A hs hp (coordinateBase A hd hs hp ho)
        (coordinateIndexEquiv A hd hs hp ho) w=1)
    (hr : 2 ≤ r)
include ε hε hA hidentity hr

theorem envelope_negative_disjoint :
    Disjoint (normalizerEnvelope A hd hs hp ho K) (Negative A hd hs hp ho K) := by
  apply envelope_disjoint_opposite (weight A hs hp b₀ coordinateHeight)
    (normalizerEnvelope A hd hs hp ho K) (Positive A hd hs hp ho K)
      (diagonalNormalizer A hd hs hp ho K) (Negative A hd hs hp ho K)
  · exact positive_le_strict A hs hp b₀ s₀ coordinateHeight (simple_height A hd hs hp ho) K
  · exact negative_le_strict_opposite A hs hp b₀ s₀ coordinateHeight (simple_height A hd hs hp ho) K
  · intro d hdD
    exact ⟨Matrix.diag (d : Matrix J₀ J₀ K),
      (diagonalNormalizer_isDiag A hd hs hp ho K ε hε hA hidentity hr d hdD).diagonal_diag.symm⟩
  · intro b hb
    obtain ⟨u,hu,d,hdD,_,he⟩ := normalizer_envelope_factor A hd hs hp ho K ε hε hA hidentity b hb
    exact ⟨u,hu,d,hdD,he⟩

theorem positive_diagonalNormalizer_disjoint :
    Disjoint (Positive A hd hs hp ho K) (diagonalNormalizer A hd hs hp ho K) := by
  apply Subgroup.disjoint_def.mpr
  intro u hu hdD
  apply strict_diagonal_eq_one (weight A hs hp b₀ coordinateHeight) u
  · exact positive_le_strict A hs hp b₀ s₀ coordinateHeight (simple_height A hd hs hp ho) K hu
  · exact ⟨Matrix.diag (u : Matrix J₀ J₀ K),
      (diagonalNormalizer_isDiag A hd hs hp ho K ε hε hA hidentity hr u hdD).diagonal_diag.symm⟩

theorem positive_diagonalNormalizer_factors_injective :
    Function.Injective (fun p : Positive A hd hs hp ho K × diagonalNormalizer A hd hs hp ho K =>
      (p.1.val : (Matrix J₀ J₀ K)ˣ) * p.2.val) :=
  Subgroup.mul_injective_of_disjoint
    (positive_diagonalNormalizer_disjoint A hd hs hp ho K ε hε hA hidentity hr)

end SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateEnvelopeIntersection
