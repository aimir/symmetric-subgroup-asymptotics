import SymmetricSubgroupAsymptotics.CFSGTrialityD4PositiveRootIndex
import SymmetricSubgroupAsymptotics.CFSGNormTwoRootDegreeSeparation
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckColumns
import SymmetricSubgroupAsymptotics.CFSGIntegralNormTwoSigns
import Mathlib.Data.Fintype.Option
import Mathlib.Order.Basic

/-! A literal integer functional separates the 24 actual D4 roots and
zero. The finite verification uses the already proved twelve-positive-root
cover. Its negative supplies a total order of the Geck root blocks, with
the four Cartan basis vectors in the single zero block. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTrialityD4SeparatingWeight
open CFSGNormTwoRootPairing CFSGIntegerMatrixPairing CFSGTrialityD4NormTwo
open CFSGTrialityD4PositiveRootIndex CFSGNormTwoGeckColumns CFSGIntegralNormTwoSigns
open CFSGNormTwoRootDegreeSeparation
local instance : DecidableEq (Roots (CartanMatrix.D 4)) := Classical.decEq _

def separatingHeight : (Fin 4 → ℤ) →ₗ[ℤ] ℤ :=
  LinearMap.proj 0 + (4 : ℤ) • LinearMap.proj 1 + (16 : ℤ) • LinearMap.proj 2 +
    (64 : ℤ) • LinearMap.proj 3

theorem separatingHeight_apply (x : Fin 4 → ℤ) :
    separatingHeight x = x 0 + 4 * x 1 + 16 * x 2 + 64 * x 3 := by
  simp only [separatingHeight, LinearMap.add_apply, LinearMap.smul_apply,
    LinearMap.proj_apply, smul_eq_mul]

abbrev WeightBlock := Option (Roots (CartanMatrix.D 4))
abbrev WeightCode := Option (Bool × OrbitIndex)

def blockVector : WeightBlock → Fin 4 → ℤ
  | none => 0
  | some k => k.val

def blockHeight (a : WeightBlock) : ℤ := -separatingHeight (blockVector a)

private def literalNegative (k : Roots (CartanMatrix.D 4)) : Roots (CartanMatrix.D 4) :=
  ⟨-k.val, by
    have hk := (negativeIndex (CartanMatrix.D 4) (CartanMatrix.D_transpose 4)
      D4_positive_definite k).property
    change integerPairing (CartanMatrix.D 4)
      (negativeIndex (CartanMatrix.D 4) (CartanMatrix.D_transpose 4) D4_positive_definite k).val
      (negativeIndex (CartanMatrix.D 4) (CartanMatrix.D_transpose 4) D4_positive_definite k).val = 2 at hk
    rw [negative_val] at hk
    exact hk⟩

def codedBlock : WeightCode → WeightBlock
  | none => none
  | some (false, a) => some (positiveRoot a).val
  | some (true, a) => some (literalNegative (positiveRoot a).val)

theorem coded_block_height_injective : Function.Injective (fun a => blockHeight (codedBlock a)) := by
  decide

theorem codedBlock_surjective : Function.Surjective codedBlock := by
  intro k
  cases k with
  | none => exact ⟨none, rfl⟩
  | some k =>
    rcases norm_two_coordinates_one_sign (CartanMatrix.D 4) (CartanMatrix.D_transpose 4)
        D4_positive_definite (fun i => by rw [CartanMatrix.D_diag 4 i]; exact even_two)
        (CartanMatrix.D_off_diag_nonpos 4) k.val k.property with hk | hk
    · obtain ⟨a, ha⟩ := positiveRoot_surjective ⟨k, hk⟩
      refine ⟨some (false, a), ?_⟩
      exact congrArg (fun p : Positive => (some p.val : WeightBlock)) ha
    · let l := literalNegative k
      have hl : ∀ i, 0 ≤ l.val i := fun i => neg_nonneg.mpr (hk i)
      obtain ⟨a, ha⟩ := positiveRoot_surjective ⟨l, hl⟩
      refine ⟨some (true, a), ?_⟩
      have hav : (positiveRoot a).val = l := congrArg Subtype.val ha
      change some (literalNegative (positiveRoot a).val) = some k
      rw [hav]
      apply congrArg some
      apply Subtype.ext
      change -(-k.val) = k.val
      exact neg_neg k.val

theorem blockHeight_injective : Function.Injective blockHeight := by
  intro a b hab
  obtain ⟨i, rfl⟩ := codedBlock_surjective a
  obtain ⟨j, rfl⟩ := codedBlock_surjective b
  exact congrArg codedBlock (coded_block_height_injective hab)

@[reducible] def blockOrder : LinearOrder WeightBlock :=
  LinearOrder.lift' blockHeight blockHeight_injective

theorem blockVector_injective : Function.Injective blockVector := by
  intro a b hab
  apply blockHeight_injective
  exact congrArg (fun x : Fin 4 → ℤ => -separatingHeight x) hab

theorem separatingHeight_simple_pos (i : Fin 4) :
    0 < separatingHeight (Pi.single i (1 : ℤ) : Fin 4 → ℤ) := by
  fin_cases i <;> decide

end SymmetricSubgroupAsymptotics.CFSGTrialityD4SeparatingWeight
