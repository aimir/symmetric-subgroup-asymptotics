import SymmetricSubgroupAsymptotics.CFSGPolarRankThreeAxisBound
import SymmetricSubgroupAsymptotics.CFSGOrthogonalBUniqueCommonNeighbour
import SymmetricSubgroupAsymptotics.CFSGOrthogonalBGramNondegenerate

/-! ALL disjoint original rank-three B singular planes have at most one
common Gamma01 neighbour. The proof excludes a singular four-space by
literal Gram nondegeneracy in dimension seven, with no classification. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalBPlaneFamilyAction
open CFSGOrthogonalBSerreMatrices CFSGOrthogonalBUnipotent CFSGOrthogonalBIntrinsicLongRoots
variable {K : Type} [Field K] [Finite K]

private theorem cross_axis_le_one (h2 : (2 : K) ≠ 0) (P Q : SingularPlanes (K := K) 0)
    (hd : Disjoint P.val Q.val) :
    Module.finrank K (P.val ⊓ (gram K 3).toBilin'.orthogonal Q.val : Submodule K (Index 3 → K)) ≤ 1 := by
  apply CFSGPolarRankThreeAxisBound.cross_axis_finrank_le_one (gram K 3).toBilin'
    (gram_nondegenerate h2 3) (gram_pairing_symmetric 3) _ P.val Q.val
    P.property.1 Q.property.1 hd P.property.2 Q.property.2
  simp [Module.finrank_fintype_fun_eq_card, Index]

private theorem cross_axis_eq_one_of_common (h2 : (2 : K) ≠ 0)
    (P Q R : SingularPlanes (K := K) 0) (hd : Disjoint P.val Q.val)
    (hPR : PlaneAdjacent 0 P.val R.val) (hQR : PlaneAdjacent 0 Q.val R.val) :
    Module.finrank K (P.val ⊓ (gram K 3).toBilin'.orthogonal Q.val : Submodule K (Index 3 → K)) = 1 := by
  have hQin : Q.val ≤ Q.val ⊔ R.val := le_sup_left
  have hRin : R.val ≤ Q.val ⊔ R.val := le_sup_right
  have hle : P.val ⊓ R.val ≤ P.val ⊓ (gram K 3).toBilin'.orthogonal Q.val := by
    intro x hx
    refine ⟨hx.1, ?_⟩
    intro q hq
    exact hQR.2.2 q (hQin hq) x (hRin hx.2)
  have hlo := Submodule.finrank_mono hle
  rw [hPR.2.1] at hlo
  have hup := cross_axis_le_one h2 P Q hd
  exact Nat.le_antisymm hup hlo

theorem rank_three_common_neighbours_subsingleton (h2 : (2 : K) ≠ 0)
    (P Q : SingularPlanes (K := K) 0) (hd : Disjoint P.val Q.val) :
    Subsingleton {R : SingularPlanes (K := K) 0 //
      PlaneAdjacent 0 P.val R.val ∧ PlaneAdjacent 0 Q.val R.val} := by
  constructor
  intro R S
  apply Subtype.ext
  exact at_most_one_common_neighbour 0 P Q R.val S.val hd
    (cross_axis_eq_one_of_common h2 P Q R.val hd R.property.1 R.property.2)
    (cross_axis_eq_one_of_common h2 Q P R.val hd.symm R.property.2 R.property.1)
    R.property.1 R.property.2 S.property.1 S.property.2

theorem rank_three_disjoint_common_neighbours_card_le_one (h2 : (2 : K) ≠ 0)
    (P Q : SingularPlanes (K := K) 0) (hd : Disjoint P.val Q.val) :
    Nat.card {R : SingularPlanes (K := K) 0 //
      PlaneAdjacent 0 P.val R.val ∧ PlaneAdjacent 0 Q.val R.val} ≤ 1 := by
  letI := rank_three_common_neighbours_subsingleton h2 P Q hd
  let f : {R : SingularPlanes (K := K) 0 //
    PlaneAdjacent 0 P.val R.val ∧ PlaneAdjacent 0 Q.val R.val} → Fin 1 := fun _ => 0
  have hf : Function.Injective f := fun _ _ _ => Subsingleton.elim _ _
  simpa only [Nat.card_fin] using Nat.card_le_card_of_injective f hf

end SymmetricSubgroupAsymptotics.CFSGOrthogonalBPlaneFamilyAction
