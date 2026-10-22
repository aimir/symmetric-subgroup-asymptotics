import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD4GlobalTypeHom
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD4PointTypeIndex

/-! The ACTUAL projective D4 automorphism subgroup preserving the
natural POINT type has index at most THREE. It need not fix the two
maximal-space types separately. Point reconstruction remains separate. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD4ResidualSpace
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDIndexPlaneFamilyAction
open CFSGOrthogonalDIndexTrialityD4RootedCliques CFSGOrthogonalDIndexTrialityD4PointTypeIndex
variable (K : Type) [Field K] [Finite K] (p : ℕ) [Fact p.Prime] [CharP K p]

def naturalPointTypeStabilizer : Subgroup (MulAut (elementaryProjective K 4)) :=
  pointStabilizer (globalTypeHom K p) (0 : Fin 3)

theorem naturalPointTypeStabilizer_index_le_three : (naturalPointTypeStabilizer K p).index ≤ 3 := by
  have h := pointStabilizer_index_le (globalTypeHom K p) (0 : Fin 3)
  norm_num [Nat.card_eq_fintype_card] at h
  exact h

theorem pointTypeStabilizer_preserves_top_type (f : naturalPointTypeStabilizer K p)
    (P : SingularPlanes K 0) (T : Set (SingularPlanes K 0))
    (hT : MaximalClique (originalPlaneAdjacent K) T) (hP : P ∈ T)
    (ht : naturalCliqueType K T = 0) :
    naturalCliqueType K (automorphismCliqueImage K p f.val T) = 0 := by
  rw [global_clique_type_formula K p f.val P T hT hP, ht]
  exact f.property

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD4ResidualSpace
