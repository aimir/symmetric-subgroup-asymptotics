import SymmetricSubgroupAsymptotics.CFSGOrthogonalBR11FrameNormalization
import SymmetricSubgroupAsymptotics.CFSGOrthogonalBR11CountNumerics
import SymmetricSubgroupAsymptotics.CFSGOrthogonalBIntersectionRecognition
import SymmetricSubgroupAsymptotics.CFSGOrthogonalBThreeTangents

/-! The actual R11 count gap, with no geometric/count input. Original
pair words, literal residual vectors, and at-most-q proportional fibres
suffice; exact projective cone cardinalities are not required. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalBPlaneFamilyAction
open CFSGOrthogonalBSerreMatrices CFSGOrthogonalBIntrinsicLongRoots
open CFSGOrthogonalBR11FrameNormalization CFSGOrthogonalBNormalizedCommonNeighbours
variable {K : Type} [Field K] [Finite K]

theorem r11_cone_le_common_neighbours (h2 : (2 : K) ≠ 0) (s : ℕ)
    (P Q : SingularPlanes (K := K) s) (h : IntersectingNonadjacent s P Q) :
    Nat.card K ^ (2 * (s + 1)) - 1 ≤ Nat.card (CommonNeighbours s P Q) * Nat.card K := by
  obtain ⟨e, he, w, hw, hwu, hc, hP, hQ⟩ := exists_normalized_frame h2 s P Q h
  have hb := normalized_cone_le_common h2 s w hw hwu hc
  have ht := isometry_common_neighbours_card s e he P Q
  rw [hP, hQ] at ht
  rw [ht] at hb
  exact hb

theorem r11_common_neighbours_large (h2 : (2 : K) ≠ 0) (s : ℕ)
    (P Q : SingularPlanes (K := K) s) (h : IntersectingNonadjacent s P Q) :
    intersectionRecognitionBound (K := K) s < Nat.card (CommonNeighbours s P Q) := by
  have hb := r11_cone_le_common_neighbours h2 s P Q h
  have hq := CFSGOrthogonalBSingularVectorCount.three_le_card K h2
  by_cases hs : s = 0
  · subst s
    exact CFSGOrthogonalBR11CountNumerics.first_residual_large _ _ hq hb
  · change (if s = 0 then 1 else (Nat.card K + 1) ^ 2) < _
    rw [if_neg hs]
    exact CFSGOrthogonalBR11CountNumerics.higher_residual_large _ _ (s + 1) hq (by omega) hb

theorem singularAction_preserves_R11 (p : ℕ) [Fact p.Prime] [CharP K p]
    (h2 : (2 : K) ≠ 0) (s : ℕ) (f : MulAut (elementaryProjective K (s + 3)))
    (P Q : SingularPlanes (K := K) s) :
    IntersectingNonadjacent s (singularActionHom p h2 s f P) (singularActionHom p h2 s f Q) ↔
      IntersectingNonadjacent s P Q :=
  singularAction_preserves_intersectingNonadjacent p h2 s
    (r11_common_neighbours_large h2 s) f P Q

end SymmetricSubgroupAsymptotics.CFSGOrthogonalBPlaneFamilyAction
