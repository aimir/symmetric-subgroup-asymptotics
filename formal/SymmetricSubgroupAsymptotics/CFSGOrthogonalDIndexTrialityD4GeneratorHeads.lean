import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD4NeighborFlags
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexRootComponents
import Mathlib.Tactic.FinCases

/-! Every original simple D4 root sends both root-plane head vectors
into the original positive space and fixes at least one of them. This
is a symbolic root-matrix calculation over every field, not a finite
group/action census. It is the concrete connectivity seed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD4ResidualSpace
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDIndexPositiveSpace
open CFSGOrthogonalDIndexPositiveGraph CFSGOrthogonalDIndexTailCoordinates
variable (K : Type) [Field K]

theorem head0_ne_zero : head0 K ≠ 0 := by
  intro he
  have hh := congrFun he (Sum.inl (0 : Fin 4))
  simpa only [head0, Pi.single_eq_same, Pi.zero_apply, one_ne_zero] using hh

theorem head1_ne_zero : head1 K ≠ 0 := by
  intro he
  have hh := congrFun he (Sum.inl (tailSecondIndex 2))
  simpa only [head1, Pi.single_eq_same, Pi.zero_apply, one_ne_zero] using hh

theorem root_head_columns_positive (neg : Bool) (i : Fin 4) (a : K) :
    ((rootTransvection K 4 neg i a : Mat K 4).col (Sum.inl 0)) ∈ positiveSpace K 4 ∧
      ((rootTransvection K 4 neg i a : Mat K 4).col (Sum.inl (tailSecondIndex 2))) ∈
        positiveSpace K 4 := by
  constructor <;> intro j <;> cases neg <;> fin_cases i <;>
    simp [rootTransvection_val, rootMatrix, positive, negative, previous,
      Matrix.col_apply, tailSecondIndex]

theorem root_fixes_head_column (neg : Bool) (i : Fin 4) (a : K) :
    (rootTransvection K 4 neg i a : Mat K 4).col (Sum.inl 0) = head0 K ∨
      (rootTransvection K 4 neg i a : Mat K 4).col (Sum.inl (tailSecondIndex 2)) = head1 K := by
  cases neg with
  | false =>
    left
    funext x
    cases x <;> fin_cases i <;>
      simp [rootTransvection_val, rootMatrix, positive, previous,
        Matrix.col_apply, Matrix.one_apply, head0, Pi.single_apply]
  | true =>
    fin_cases i
    · right
      funext x
      cases x <;>
        simp [rootTransvection_val, rootMatrix, positive, negative,
          Matrix.col_apply, Matrix.one_apply, head1, tailSecondIndex, Pi.single_apply]
    all_goals
      left
      funext x
      cases x <;>
        simp [rootTransvection_val, rootMatrix, positive, negative, previous,
          Matrix.col_apply, Matrix.one_apply, head0, Pi.single_apply]

theorem root_fixes_head (neg : Bool) (i : Fin 4) (a : K) :
    ambientLinearEquiv K 4 (rootTransvection K 4 neg i a) (head0 K) = head0 K ∨
      ambientLinearEquiv K 4 (rootTransvection K 4 neg i a) (head1 K) = head1 K := by
  change (rootTransvection K 4 neg i a : Mat K 4) *ᵥ head0 K = head0 K ∨
    (rootTransvection K 4 neg i a : Mat K 4) *ᵥ head1 K = head1 K
  simpa only [head0, head1, Matrix.mulVec_single_one] using root_fixes_head_column K neg i a

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD4ResidualSpace
