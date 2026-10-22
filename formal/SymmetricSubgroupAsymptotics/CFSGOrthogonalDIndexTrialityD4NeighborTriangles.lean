import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD4NeighborFlags
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD4ThreeIncidence

/-! Literal Grassmann triangles in the D4 neighbour residue. Distinct
intersection points force equality of the singular three-spaces;
every adjacent pair has an actual common maximal singular extension. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD4ResidualSpace
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDIndexBundledQuadratic
open CFSGOrthogonalDIndexQuadraticNeighborPlane CFSGOrthogonalDIndexQuadraticCorrection
variable (K : Type) [Field K]

def NeighborAdjacent (S T : Neighbors K) : Prop :=
  S ≠ T ∧ Module.finrank K ↥(S.val ⊓ T.val) = 1 ∧
    ∀ x ∈ S.val ⊔ T.val, splitQuadraticForm K 4 x = 0

private theorem line_inf_eq_bot_of_ne
    (A B : Submodule K (Index 4 → K))
    (hA : Module.finrank K A = 1) (hB : Module.finrank K B = 1) (hne : A ≠ B) :
    A ⊓ B = ⊥ := by
  by_contra hh
  have hp : 0 < Module.finrank K ↥(A ⊓ B) :=
    Nat.pos_of_ne_zero (fun hz => hh (Submodule.finrank_eq_zero.mp hz))
  have heA : A ⊓ B = A := Submodule.eq_of_le_of_finrank_le inf_le_left (by omega)
  have heB : A ⊓ B = B := Submodule.eq_of_le_of_finrank_le inf_le_right (by omega)
  exact hne (heA.symm.trans heB)

theorem rootPlane_eq_sup_neighbor_points (S T : Neighbors K)
    (hne : neighborPoint K S ≠ neighborPoint K T) :
    rootPlane K = (neighborPoint K S).val ⊔ (neighborPoint K T).val := by
  have hval : (neighborPoint K S).val ≠ (neighborPoint K T).val :=
    fun h => hne (Subtype.ext h)
  have hinf := line_inf_eq_bot_of_ne K _ _
    (neighborPoint K S).property.1 (neighborPoint K T).property.1 hval
  have hd := Submodule.finrank_sup_add_finrank_inf_eq
    (neighborPoint K S).val (neighborPoint K T).val
  rw [hinf, finrank_bot, (neighborPoint K S).property.1,
    (neighborPoint K T).property.1] at hd
  apply Eq.symm
  apply Submodule.eq_of_le_of_finrank_le
    (sup_le (neighborPoint K S).property.2 (neighborPoint K T).property.2)
  rw [rootPlane_finrank]
  omega

theorem neighbor_threeSpace_eq_of_points_ne (S T : Neighbors K)
    (hST : Module.finrank K ↥(S.val ⊓ T.val) = 1)
    (hne : neighborPoint K S ≠ neighborPoint K T) :
    neighborThreeSpace K S = neighborThreeSpace K T := by
  have hR : rootPlane K ≤ S.val ⊔ T.val := by
    exact (rootPlane_eq_sup_neighbor_points K S T hne).le.trans
      (sup_le ((neighbor_point_le K S).trans le_sup_left)
        ((neighbor_point_le K T).trans le_sup_right))
  have hd : Module.finrank K ↥(S.val ⊔ T.val) = 3 := by
    have hh := Submodule.finrank_sup_add_finrank_inf_eq S.val T.val
    rw [S.property.1, T.property.1, hST] at hh
    omega
  have hS : (neighborThreeSpace K S).val = S.val ⊔ T.val :=
    Submodule.eq_of_le_of_finrank_le (sup_le hR le_sup_left)
      (by rw [hd, (neighborThreeSpace K S).property.1])
  have hT : (neighborThreeSpace K T).val = S.val ⊔ T.val :=
    Submodule.eq_of_le_of_finrank_le (sup_le hR le_sup_right)
      (by rw [hd, (neighborThreeSpace K T).property.1])
  exact Subtype.ext (hS.trans hT.symm)

theorem neighbor_parameters_eq_of_points_ne (S T : Neighbors K)
    (hST : Module.finrank K ↥(S.val ⊓ T.val) = 1)
    (hne : neighborPoint K S ≠ neighborPoint K T) :
    neighborOppositeParameters K S = neighborOppositeParameters K T :=
  congrArg (fun W => (threeExtensionRulingEquiv K).symm W)
    (neighbor_threeSpace_eq_of_points_ne K S T hST hne)

theorem neighbor_triangle_singular (S T : Neighbors K) (hST : NeighborAdjacent K S T) :
    ∀ x ∈ rootPlane K ⊔ S.val ⊔ T.val, splitQuadraticForm K 4 x = 0 := by
  apply singular_sup _ _ _ S.property.2.2
  · intro t ht
    exact T.property.2.2 t (Submodule.mem_sup_right ht)
  · intro x hx t ht
    obtain ⟨r, hr, s, hs, rfl⟩ := Submodule.mem_sup.mp hx
    have hrt := polar_zero_of_singular (splitQuadraticForm K 4)
      (rootPlane K ⊔ T.val) T.property.2.2 r t
      (Submodule.mem_sup_left hr) (Submodule.mem_sup_right ht)
    have hst := polar_zero_of_singular (splitQuadraticForm K 4)
      (S.val ⊔ T.val) hST.2.2 s t
      (Submodule.mem_sup_left hs) (Submodule.mem_sup_right ht)
    rw [map_add, LinearMap.add_apply, hrt, hst, zero_add]

theorem neighbor_triangle_finrank_bounds (S T : Neighbors K)
    (hST : Module.finrank K ↥(S.val ⊓ T.val) = 1) :
    3 ≤ Module.finrank K ↥(rootPlane K ⊔ S.val ⊔ T.val) ∧
      Module.finrank K ↥(rootPlane K ⊔ S.val ⊔ T.val) ≤ 4 := by
  have hlow : 3 ≤ Module.finrank K ↥(rootPlane K ⊔ S.val ⊔ T.val) := by
    have hh := Submodule.finrank_mono
      (le_sup_left : (neighborThreeSpace K S).val ≤ rootPlane K ⊔ S.val ⊔ T.val)
    rw [(neighborThreeSpace K S).property.1] at hh
    exact hh
  have hline : 1 ≤ Module.finrank K ↥((rootPlane K ⊔ S.val) ⊓ T.val) := by
    have hh := Submodule.finrank_mono
      (inf_le_inf (le_sup_right : S.val ≤ rootPlane K ⊔ S.val)
        (le_rfl : T.val ≤ T.val))
    rw [hST] at hh
    exact hh
  have hh := Submodule.finrank_sup_add_finrank_inf_eq (rootPlane K ⊔ S.val) T.val
  change Module.finrank K ↥(rootPlane K ⊔ S.val ⊔ T.val) +
    Module.finrank K ↥((rootPlane K ⊔ S.val) ⊓ T.val) =
      Module.finrank K (neighborThreeSpace K S).val + Module.finrank K T.val at hh
  rw [(neighborThreeSpace K S).property.1, T.property.1] at hh
  exact ⟨hlow, by omega⟩

theorem adjacent_neighbors_common_maximal (S T : Neighbors K) (hST : NeighborAdjacent K S T) :
    ∃ M : MaximalExtensions K,
      (neighborThreeSpace K S).val ≤ M.val ∧ (neighborThreeSpace K T).val ≤ M.val := by
  let W : Submodule K (Index 4 → K) := rootPlane K ⊔ S.val ⊔ T.val
  obtain ⟨hlo, hhi⟩ := neighbor_triangle_finrank_bounds K S T hST.2.1
  have hdim : Module.finrank K W = 3 ∨ Module.finrank K W = 4 := by
    change 3 ≤ Module.finrank K W at hlo
    change Module.finrank K W ≤ 4 at hhi
    omega
  rcases hdim with h3 | h4
  · have hS : (neighborThreeSpace K S).val = W :=
      Submodule.eq_of_le_of_finrank_le le_sup_left
        (by rw [h3, (neighborThreeSpace K S).property.1])
    let p := (neighborOppositeParameters K S).1
    refine ⟨columnMaximalExtension K p, ?_, ?_⟩
    · rw [neighbor_threeSpace_intersection]
      exact inf_le_left
    · apply le_trans (sup_le (le_sup_left.trans le_sup_left) le_sup_right :
        (neighborThreeSpace K T).val ≤ W)
      rw [← hS, neighbor_threeSpace_intersection]
      exact inf_le_left
  · exact ⟨⟨W, h4, neighbor_triangle_singular K S T hST,
      le_sup_left.trans le_sup_left⟩, le_sup_left,
      sup_le (le_sup_left.trans le_sup_left) le_sup_right⟩

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD4ResidualSpace
