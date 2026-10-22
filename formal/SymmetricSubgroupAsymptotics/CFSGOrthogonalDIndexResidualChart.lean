import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexBundledQuadratic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith

/-! A normalized q^4 chart of the literal split six-space cone, embedded
in every original residual D space of rank at least three. The fixed
positive coordinate is one, so scalar-proportional chart vectors are
equal. No quadric census or projective counting formula is used. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexResidualChart
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDIndexQuadraticForm
open CFSGOrthogonalDIndexBundledQuadratic
variable (K : Type) [Field K]

def oneIndex (s : ℕ) : Fin (s + 3) := ⟨1, by omega⟩
def twoIndex (s : ℕ) : Fin (s + 3) := ⟨2, by omega⟩

def normalizedChart (s : ℕ) (p : Fin 4 → K) : Index (s + 3) → K :=
  Sum.elim
    (Pi.single 0 1 + Pi.single (oneIndex s) (p 0) + Pi.single (twoIndex s) (p 1))
    (Pi.single 0 (-(p 0 * p 2 + p 1 * p 3)) +
      Pi.single (oneIndex s) (p 2) + Pi.single (twoIndex s) (p 3))

@[simp] theorem normalizedChart_positive_zero (s : ℕ) (p : Fin 4 → K) :
    normalizedChart K s p (Sum.inl 0) = 1 := by
  simp [normalizedChart, oneIndex, twoIndex, Fin.ext_iff]

@[simp] theorem normalizedChart_positive_one (s : ℕ) (p : Fin 4 → K) :
    normalizedChart K s p (Sum.inl (oneIndex s)) = p 0 := by
  simp [normalizedChart, oneIndex, twoIndex, Fin.ext_iff]

@[simp] theorem normalizedChart_positive_two (s : ℕ) (p : Fin 4 → K) :
    normalizedChart K s p (Sum.inl (twoIndex s)) = p 1 := by
  simp [normalizedChart, oneIndex, twoIndex, Fin.ext_iff]

@[simp] theorem normalizedChart_negative_one (s : ℕ) (p : Fin 4 → K) :
    normalizedChart K s p (Sum.inr (oneIndex s)) = p 2 := by
  simp [normalizedChart, oneIndex, twoIndex, Fin.ext_iff]

@[simp] theorem normalizedChart_negative_two (s : ℕ) (p : Fin 4 → K) :
    normalizedChart K s p (Sum.inr (twoIndex s)) = p 3 := by
  simp [normalizedChart, oneIndex, twoIndex, Fin.ext_iff]

theorem normalizedChart_ne_zero (s : ℕ) (p : Fin 4 → K) : normalizedChart K s p ≠ 0 := by
  intro he
  have hh := congrFun he (Sum.inl 0)
  exact one_ne_zero (by simpa only [normalizedChart_positive_zero, Pi.zero_apply] using hh)

theorem normalizedChart_singular (s : ℕ) (p : Fin 4 → K) :
    splitQuadraticForm K (s + 3) (normalizedChart K s p) = 0 := by
  rw [splitQuadraticForm_apply]
  change ((Pi.single (0 : Fin (s + 3)) (1 : K) +
      Pi.single (oneIndex s) (p 0) + Pi.single (twoIndex s) (p 1)) : Fin (s + 3) → K) ⬝ᵥ
    ((Pi.single (0 : Fin (s + 3)) (-(p 0 * p 2 + p 1 * p 3)) +
      Pi.single (oneIndex s) (p 2) + Pi.single (twoIndex s) (p 3)) : Fin (s + 3) → K) = (0 : K)
  simp only [add_dotProduct, single_dotProduct, one_mul]
  simp [Pi.single_apply, oneIndex, twoIndex, Fin.ext_iff] <;> ring

theorem normalizedChart_injective (s : ℕ) : Function.Injective (normalizedChart K s) := by
  intro p q he
  have h0 := congrFun he (Sum.inl (oneIndex s))
  have h1 := congrFun he (Sum.inl (twoIndex s))
  have h2 := congrFun he (Sum.inr (oneIndex s))
  have h3 := congrFun he (Sum.inr (twoIndex s))
  simp only [normalizedChart_positive_one] at h0
  simp only [normalizedChart_positive_two] at h1
  simp only [normalizedChart_negative_one] at h2
  simp only [normalizedChart_negative_two] at h3
  funext i
  fin_cases i
  · exact h0
  · exact h1
  · exact h2
  · exact h3

theorem normalizedChart_eq_of_proportional (s : ℕ) (p q : Fin 4 → K) (a : K)
    (he : normalizedChart K s p = a • normalizedChart K s q) : p = q := by
  have hh := congrFun he (Sum.inl 0)
  have ha : a = 1 := by
    simpa only [normalizedChart_positive_zero, Pi.smul_apply, smul_eq_mul, mul_one] using hh.symm
  apply normalizedChart_injective K s
  simpa only [ha, one_smul] using he

omit [Field K] in
theorem parameter_card : Nat.card (Fin 4 → K) = Nat.card K ^ 4 := by
  rw [Nat.card_fun, Nat.card_fin]

theorem fourth_power_gt_disjoint_bound (q : ℕ) (hq : 2 ≤ q) :
    (q + 1) ^ 2 < q ^ 4 := by
  have hm : 2 * q ≤ q * q := Nat.mul_le_mul_right q hq
  have hs : q + 1 < q ^ 2 := by nlinarith
  have h := Nat.pow_lt_pow_left hs (by decide : 2 ≠ 0)
  simpa only [← pow_mul] using h

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexResidualChart
