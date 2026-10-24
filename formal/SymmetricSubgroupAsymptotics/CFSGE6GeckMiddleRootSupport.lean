import SymmetricSubgroupAsymptotics.CFSGE6GeckMiddleRootDegrees
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinatePositiveRootGenerators
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith

/-! The zero-functional positive E6 roots for the middle A3 support
are exactly six explicit integer vectors. The proof uses the norm-two
equation on three coordinates, without enumerating the E6 root type. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical Matrix
namespace SymmetricSubgroupAsymptotics.CFSGE6GeckMiddleRootSupport
open CFSGE6GeckMiddleRootDegrees CFSGExceptionalNormTwoBases
open CFSGExceptionalCartanPositiveDefinite CFSGNormTwoRootPairing
open CFSGIntegerMatrixPairing CFSGNormTwoCoordinatePositiveRootGenerators
local notation "A" => CartanMatrix.E₆

def middleVector : Fin 6 → (Fin 6 → ℤ) :=
  ![![0,0,1,0,0,0], ![0,0,0,1,0,0], ![0,0,0,0,1,0],
    ![0,0,1,1,0,0], ![0,0,0,1,1,0], ![0,0,1,1,1,0]]

private abbrev coordinate (i : Fin 6) : (Fin 6 → ℤ) →ₗ[ℤ] ℤ := LinearMap.proj i

def outsideHeight : (Fin 6 → ℤ) →ₗ[ℤ] ℤ :=
  (coordinate 0 + coordinate 1) + coordinate 5

theorem outsideHeight_apply (v : Fin 6 → ℤ) :
    outsideHeight v = v 0 + v 1 + v 5 := rfl

theorem outsideHeight_nonnegative (k : PositiveRoot A) : 0 ≤ outsideHeight k.val.val :=
  add_nonneg (add_nonneg (k.property 0) (k.property 1)) (k.property 5)

private theorem three_norm_two (a b c : ℤ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hn : a^2 + (a-b)^2 + (b-c)^2 + c^2 = 2) :
    ∃ i : Fin 6, (![0,0,a,b,c,0] : Fin 6 → ℤ) = middleVector i := by
  have ha1 : a ≤ 1 := by nlinarith [sq_nonneg (a-b), sq_nonneg (b-c), sq_nonneg c, sq_nonneg (a-1)]
  have hc1 : c ≤ 1 := by nlinarith [sq_nonneg (a-b), sq_nonneg (b-c), sq_nonneg a, sq_nonneg (c-1)]
  have hba : b ≤ a+1 := by nlinarith [sq_nonneg a, sq_nonneg c, sq_nonneg (b-c), sq_nonneg (b-a-1)]
  have hb2 : b ≤ 2 := by omega
  interval_cases a <;> interval_cases b <;> interval_cases c <;> norm_num at hn
  all_goals decide +kernel

theorem positive_root_zero_outside_iff (k : PositiveRoot A) :
    outsideHeight k.val.val = 0 ↔ ∃ i : Fin 6, k.val.val = middleVector i := by
  constructor
  · intro hk
    have h0 : k.val.val 0 = 0 := by
      have := k.property 0
      have := k.property 1
      have := k.property 5
      rw [outsideHeight_apply] at hk
      omega
    have h1 : k.val.val 1 = 0 := by
      have := k.property 0
      have := k.property 1
      have := k.property 5
      rw [outsideHeight_apply] at hk
      omega
    have h5 : k.val.val 5 = 0 := by
      have := k.property 0
      have := k.property 1
      have := k.property 5
      rw [outsideHeight_apply] at hk
      omega
    have he : k.val.val = ![0,0,k.val.val 2,k.val.val 3,k.val.val 4,0] := by
      funext i
      fin_cases i <;> simp [h0,h1,h5]
    have hn := k.val.property
    rw [he] at hn
    have hp : k.val.val 2 ^ 2 + (k.val.val 2-k.val.val 3)^2 +
        (k.val.val 3-k.val.val 4)^2 + k.val.val 4 ^ 2 = 2 := by
      norm_num [integerPairing, Matrix.toBilin'_apply', dotProduct,
        Matrix.mulVec, Fin.sum_univ_succ, CartanMatrix.E₆] at hn
      nlinarith [hn]
    obtain ⟨i,hi⟩ := three_norm_two (k.val.val 2) (k.val.val 3) (k.val.val 4)
      (k.property 2) (k.property 3) (k.property 4) hp
    exact ⟨i,he.trans hi⟩
  · rintro ⟨i,hi⟩
    rw [hi]
    fin_cases i <;> rfl

end SymmetricSubgroupAsymptotics.CFSGE6GeckMiddleRootSupport
