import SymmetricSubgroupAsymptotics.CFSGOrthogonalDGenerationSignedRootConjugation
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDGenerationRootArrays

/-! Exactly the output lines that commute with the short factor of the
cleaned D generator. The endpoint at negative coordinate zero is included;
no assumption that the pure Weyl element is already generated is made. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDGenerationCleanedRootCommutation
open Matrix CFSGOrthogonalDSerreMatrices CFSGOrthogonalDGenerationInitialElements
open CFSGOrthogonalDGenerationInitialRootMatrices CFSGOrthogonalDGenerationForkTorus
open CFSGOrthogonalDGenerationRootArrays CFSGOrthogonalDBinaryCyclePermutation
open CFSGOrthogonalDGenerationSignedRootConjugation
variable (K : Type) [Field K]

theorem initial_commutes_moving (s : ℕ) (j : Fin (s + 4))
    (hj0 : j ≠ 0) (_hj1 : j ≠ second s) (side : Bool) (a b : K) :
    Commute ((initialShortRoot K s a).val : Mat K (s + 4))
      (rootArray K (Sum.inl j) (if side then Sum.inr (last (s + 2))
        else Sum.inl (last (s + 2))) b) := by
  change _ * _ = _ * _
  rw [initialShortRoot_coe]
  cases side <;>
    simp [rootArray, paired, mul_add, add_mul, mul_sub, sub_mul,
      hj0, Ne.symm hj0, last_ne_zero, Ne.symm (last_ne_zero s),
      second_ne_last, Ne.symm (second_ne_last s)] <;> abel

theorem initial_commutes_endpoint (s : ℕ) (side : Bool) (a b : K) :
    Commute ((initialShortRoot K s a).val : Mat K (s + 4))
      (rootArray K (Sum.inr (0 : Fin (s + 4))) (if side then Sum.inr (last (s + 2))
        else Sum.inl (last (s + 2))) b) := by
  change _ * _ = _ * _
  rw [initialShortRoot_coe]
  cases side <;>
    simp [rootArray, paired, mul_add, add_mul, mul_sub, sub_mul,
      second_ne_zero, Ne.symm (second_ne_zero s), last_ne_zero, Ne.symm (last_ne_zero s),
      second_ne_last, Ne.symm (second_ne_last s)] <;> abel

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDGenerationCleanedRootCommutation
