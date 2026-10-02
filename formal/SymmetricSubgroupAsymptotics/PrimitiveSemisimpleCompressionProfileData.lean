import SymmetricSubgroupAsymptotics.SemisimpleNormalChart
import Mathlib.Tactic

/-! # Structural data for primitive semisimple compression -/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics

theorem primitiveSocle_degree_le_power
    {a ell q : ℕ} (ha : 2 ≤ a) (hell : 2 ≤ ell)
    (hbase : 4 * q ≤ ell ^ 2) :
    2 * (a * q) ≤ ell ^ a := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le ha
  have hk : ∀ k : ℕ, 2 * ((2 + k) * q) ≤ ell ^ (2 + k) := by
    intro k
    induction k with
    | zero =>
      calc
        2 * ((2 + 0) * q) = 4 * q := by ring
        _ ≤ ell ^ 2 := hbase
        _ = ell ^ (2 + 0) := by ring
    | succ k ih =>
      have hstep : k + 3 ≤ (k + 2) * ell := by
        have hsmall : k + 3 ≤ 2 * (k + 2) := by omega
        have hmul : 2 * (k + 2) ≤ ell * (k + 2) :=
          Nat.mul_le_mul_right (k + 2) hell
        simpa only [Nat.mul_comm] using hsmall.trans hmul
      have ih' : 2 * ((k + 2) * q) ≤ ell ^ (k + 2) := by
        simpa only [Nat.add_comm] using ih
      calc
        2 * ((2 + Nat.succ k) * q) = 2 * ((k + 3) * q) := by
          rw [show 2 + Nat.succ k = k + 3 by omega]
        _ = (k + 3) * (2 * q) := by ring
        _ ≤ ((k + 2) * ell) * (2 * q) :=
          Nat.mul_le_mul_right (2 * q) hstep
        _ = (2 * ((k + 2) * q)) * ell := by ring
        _ ≤ (ell ^ (k + 2)) * ell := Nat.mul_le_mul_right ell ih'
        _ = ell ^ ((k + 2) + 1) := (pow_succ ell (k + 2)).symm
        _ = ell ^ (2 + Nat.succ k) := by
          congr 1
          omega
  exact hk k

/-- The structural and numerical data before conversion to the local
compression interface. -/
structure PrimitiveSemisimpleCompressionProfile
    (L : Type) [Group L] (r : ℕ) where
  E : Subgroup L
  [E_normal : E.Normal]
  chart : SemisimpleNormalChart E
  factorCount : ℕ
  factorCount_pos : 0 < factorCount
  leastIndex : ℕ
  leastIndex_two_le : 2 ≤ leastIndex
  outerOrder : ℕ
  outerOrder_pos : 0 < outerOrder
  quotientAction :
    (L ⧸ E) →* Equiv.Perm (Fin (factorCount * outerOrder))
  quotientAction_injective : Function.Injective quotientAction
  primitive_index_lower : leastIndex ^ factorCount ≤ r
  multiple_factor_base : 4 * outerOrder ≤ leastIndex ^ 2
  large_simple_base : 30 ≤ leastIndex → 2 * outerOrder ≤ leastIndex

attribute [instance] PrimitiveSemisimpleCompressionProfile.E_normal

end SymmetricSubgroupAsymptotics

end
