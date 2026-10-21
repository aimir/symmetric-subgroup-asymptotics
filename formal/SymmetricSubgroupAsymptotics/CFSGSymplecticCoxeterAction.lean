import SymmetricSubgroupAsymptotics.CFSGSymplecticCoxeterPrefixAction
import Mathlib.Algebra.CharP.Two

/-! The complete actual signed Coxeter cycle. In characteristic two
the signs disappear, giving the literal cycle through all positive then
all negative coordinates, without a group-recognition hypothesis. -/
set_option autoImplicit false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGSymplecticSerreMatrices

theorem terminal_basis_fixed (K : Type) [Field K] (r : ℕ) (side : Bool)
    (j : Fin (r + 1)) (hj : j ≠ Fin.last r) :
    ((simpleWeyl K (r + 1) (Fin.last r)).val : Mat K (r + 1)) *ᵥ
      coordinateBasis K r side j = coordinateBasis K r side j := by
  cases side
  · exact simpleWeyl_terminal_other K r (Sum.inl j)
      (fun h => hj (Sum.inl.inj h)) (by intro h; cases h)
  · exact simpleWeyl_terminal_other K r (Sum.inr j)
      (by intro h; cases h) (fun h => hj (Sum.inr.inj h))

theorem terminal_natural_basis_fixed (K : Type) [Field K] (r : ℕ) (side : Bool)
    (j : ℕ) (hj : j < r) :
    ((simpleWeyl K (r + 1) (Fin.last r)).val : Mat K (r + 1)) *ᵥ
      naturalCoordinateBasis K r side j = naturalCoordinateBasis K r side j := by
  let v : Fin (r + 1) := ⟨j, Nat.lt_succ_of_lt hj⟩
  have hv : v ≠ Fin.last r := by
    intro h
    have hh := congrArg Fin.val h
    change j = r at hh
    omega
  have h := terminal_basis_fixed K r side v hv
  simpa only [← naturalCoordinateBasis_val] using h

theorem terminal_natural_positive (K : Type) [Field K] (r : ℕ) :
    ((simpleWeyl K (r + 1) (Fin.last r)).val : Mat K (r + 1)) *ᵥ
      naturalCoordinateBasis K r false r = naturalCoordinateBasis K r true r := by
  have h := simpleWeyl_terminal_positive K r
  change ((simpleWeyl K (r + 1) (Fin.last r)).val : Mat K (r + 1)) *ᵥ
    coordinateBasis K r false (Fin.last r) = coordinateBasis K r true (Fin.last r) at h
  simpa only [← naturalCoordinateBasis_val] using h

theorem terminal_natural_negative (K : Type) [Field K] (r : ℕ) :
    ((simpleWeyl K (r + 1) (Fin.last r)).val : Mat K (r + 1)) *ᵥ
      naturalCoordinateBasis K r true r = -naturalCoordinateBasis K r false r := by
  have h := simpleWeyl_terminal_negative K r
  change ((simpleWeyl K (r + 1) (Fin.last r)).val : Mat K (r + 1)) *ᵥ
    coordinateBasis K r true (Fin.last r) = -coordinateBasis K r false (Fin.last r) at h
  simpa only [← naturalCoordinateBasis_val] using h

theorem coxeterWeyl_basis_shift (K : Type) [Field K] (r : ℕ) (side : Bool)
    (j : ℕ) (hj : j < r) :
    ((coxeterWeyl K r).val : Mat K (r + 1)) *ᵥ naturalCoordinateBasis K r side j =
      naturalCoordinateBasis K r side (j + 1) := by
  change (((chainWeylPrefix K r r).val : Mat K (r + 1)) *
    ((simpleWeyl K (r + 1) (Fin.last r)).val : Mat K (r + 1))) *ᵥ
      naturalCoordinateBasis K r side j = _
  rw [← Matrix.mulVec_mulVec, terminal_natural_basis_fixed K r side j hj,
    chainWeylPrefix_basis K r r le_rfl side j hj.le]
  simp only [hj, if_true]

theorem coxeterWeyl_basis_positive_last (K : Type) [Field K] (r : ℕ) :
    ((coxeterWeyl K r).val : Mat K (r + 1)) *ᵥ naturalCoordinateBasis K r false r =
      (-1 : K) ^ r • naturalCoordinateBasis K r true 0 := by
  change (((chainWeylPrefix K r r).val : Mat K (r + 1)) *
    ((simpleWeyl K (r + 1) (Fin.last r)).val : Mat K (r + 1))) *ᵥ
      naturalCoordinateBasis K r false r = _
  rw [← Matrix.mulVec_mulVec, terminal_natural_positive,
    chainWeylPrefix_basis K r r le_rfl true r le_rfl]
  simp only [lt_self_iff_false, if_false, if_true]

theorem coxeterWeyl_basis_negative_last (K : Type) [Field K] (r : ℕ) :
    ((coxeterWeyl K r).val : Mat K (r + 1)) *ᵥ naturalCoordinateBasis K r true r =
      (-1 : K) ^ (r + 1) • naturalCoordinateBasis K r false 0 := by
  change (((chainWeylPrefix K r r).val : Mat K (r + 1)) *
    ((simpleWeyl K (r + 1) (Fin.last r)).val : Mat K (r + 1))) *ᵥ
      naturalCoordinateBasis K r true r = _
  rw [← Matrix.mulVec_mulVec, terminal_natural_negative, Matrix.mulVec_neg,
    chainWeylPrefix_basis K r r le_rfl false r le_rfl]
  simp only [lt_self_iff_false, if_false, if_true, pow_succ, mul_neg_one, neg_smul]

theorem coxeterWeyl_binary_positive_last (K : Type) [Field K] [CharP K 2] (r : ℕ) :
    ((coxeterWeyl K r).val : Mat K (r + 1)) *ᵥ naturalCoordinateBasis K r false r =
      naturalCoordinateBasis K r true 0 := by
  simpa only [CharTwo.neg_eq, one_pow, one_smul] using coxeterWeyl_basis_positive_last K r

theorem coxeterWeyl_binary_negative_last (K : Type) [Field K] [CharP K 2] (r : ℕ) :
    ((coxeterWeyl K r).val : Mat K (r + 1)) *ᵥ naturalCoordinateBasis K r true r =
      naturalCoordinateBasis K r false 0 := by
  simpa only [CharTwo.neg_eq, one_pow, one_smul] using coxeterWeyl_basis_negative_last K r

end SymmetricSubgroupAsymptotics.CFSGSymplecticSerreMatrices
