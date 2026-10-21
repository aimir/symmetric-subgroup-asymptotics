import SymmetricSubgroupAsymptotics.CFSGSerreRootOperatorInvertible
import Mathlib.Tactic.IntervalCases

/-! In characteristic two the original four-term Serre root polynomial
is an involution. The integral binomial coefficients 2, 6 and 20 kill the
squares of its three positive divided powers; no uniform nilpotence or
additive root-parameter theorem is required. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical BigOperators
namespace SymmetricSubgroupAsymptotics.CFSGSerreCharacteristicTwoRoots
open CFSG.Models.Chevalley CFSGSerreDividedPowers CFSGSerreLocalNilpotence
variable {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ)
  (K : Type) [Field K] [CharP K 2]

theorem module_add_self_eq_zero {M : Type*} [AddCommGroup M] [Module K M] (x : M) :
    x + x = 0 := by
  rw [← two_smul K x, CharP.ofNat_eq_zero K 2, zero_smul]

private theorem even_nsmul_eq_zero (k : ℕ) (hk : Even k)
    (D : Module.End K (Space A K)) : k • D = 0 := by
  obtain ⟨m, rfl⟩ := hk
  rw [add_smul]
  exact module_add_self_eq_zero K (m • D)

theorem dividedPower_sq_zero (negative : Bool) (i : Fin n) (k : ℕ)
    (hk : 0 < k) (hk3 : k ≤ 3) :
    ((integralOperator A negative i k).baseChange K) ^ 2 = 0 := by
  rw [pow_two, baseChangedIntegralOperator_mul]
  apply even_nsmul_eq_zero
  interval_cases k <;> decide

private theorem add_sq_of_commute (D E : Module.End K (Space A K))
    (hDE : Commute D E) : (D + E) ^ 2 = D ^ 2 + E ^ 2 := by
  rw [hDE.add_sq]
  simp only [two_mul, module_add_self_eq_zero K, zero_mul, add_zero]

theorem rootOperator_sq (negative : Bool) (i : Fin n) (t : K) :
    rootOperator A K negative i t ^ 2 = 1 := by
  let D : ℕ → Module.End K (Space A K) :=
    fun k => t ^ k • (integralOperator A negative i k).baseChange K
  have hcomm (k l : ℕ) : Commute (D k) (D l) :=
    ((baseChangedIntegralOperator_commute A K negative i k l).smul_left (t ^ k)).smul_right
      (t ^ l)
  have hsq (k : ℕ) (hk : 0 < k) (hk3 : k ≤ 3) : D k ^ 2 = 0 := by
    dsimp only [D]
    rw [pow_two, smul_mul_assoc, mul_smul_comm, ← pow_two,
      dividedPower_sq_zero A K negative i k hk hk3, smul_zero, smul_zero]
  have hsum : (D 1 + D 2 + D 3) ^ 2 = 0 := by
    rw [add_sq_of_commute A K (D 1 + D 2) (D 3)
      ((hcomm 1 3).add_left (hcomm 2 3)),
      add_sq_of_commute A K (D 1) (D 2) (hcomm 1 2),
      hsq 1 (by decide) (by decide), hsq 2 (by decide) (by decide),
      hsq 3 (by decide) (by decide), zero_add, zero_add]
  have heq : rootOperator A K negative i t = 1 + (D 1 + D 2 + D 3) := by
    rw [rootOperator_eq_one_add_positiveRootPart]
    simp [positiveRootPart, D, Finset.sum_range_succ, add_assoc]
  rw [heq, add_sq_of_commute A K 1 (D 1 + D 2 + D 3) (Commute.one_left _),
    hsum, one_pow, add_zero]

theorem rootEquiv_sq (negative : Bool) (i : Fin n) (t : K) :
    rootEquiv A K negative i t ^ 2 = 1 := by
  apply LinearEquiv.toLinearMap_injective
  change rootOperator A K negative i t ^ 2 = 1
  exact rootOperator_sq A K negative i t

end SymmetricSubgroupAsymptotics.CFSGSerreCharacteristicTwoRoots
