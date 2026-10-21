import SymmetricSubgroupAsymptotics.CFSGSolubleOrbitProductContainers
import SymmetricSubgroupAsymptotics.CFSGSolubleWreathContainersConstruction

/-! A constructed actual labelled soluble envelope menu on all n points.
The orbit-product budget retains only n^n label maps and one transitive
budget at the original total degree. No published Pyber input is used. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGSolubleFullContainerCover
open CFSGSolubleWreathContainers CFSGSolublePrimitiveContainers
open CFSGSolubleOrbitProductContainers CFSGOrdinaryContainerCoverFormula

def cover (b : ℕ) : SolubleContainerCover b := fullCover transitiveCover b

theorem cover_real_card_le (b : ℕ) :
    (Nat.card (cover b).Index : ℝ) ≤
      (b : ℝ)^b*(2 : ℝ)^(((32*logBudget b : ℕ) : ℝ)*b) := by
  apply index_real_card_le transitiveCover b (((32*logBudget b : ℕ) : ℝ))
  intro d hd
  rw [←Nat.cast_mul,Real.rpow_natCast]
  exact_mod_cast transitiveCover_card_le_common_budget hd

/-- A convenient native bound, including every original orbit label. -/
theorem cover_card_le (b : ℕ) : Nat.card (cover b).Index ≤ 2^(33*b*logBudget b) := by
  have hc := cover_real_card_le b
  have hn : Nat.card (cover b).Index ≤ b^b*2^((32*logBudget b)*b) := by
    rw [←Nat.cast_mul,Real.rpow_natCast] at hc
    exact_mod_cast hc
  have hl : b^b ≤ 2^(b*logBudget b) := by
    calc
      b^b ≤ (2^logSize b)^b := Nat.pow_le_pow_left (card_le_two_pow_logSize b) b
      _ = 2^(logSize b*b) := (pow_mul _ _ _).symm
      _ ≤ _ := Nat.pow_le_pow_right (by decide : 0<2)
        (by nlinarith [Nat.mul_le_mul_right b (logSize_le_logBudget b)])
  apply hn.trans
  calc
    _ ≤ 2^(b*logBudget b)*2^((32*logBudget b)*b) := Nat.mul_le_mul_right _ hl
    _ = _ := by rw [←pow_add];congr 1;ring

end SymmetricSubgroupAsymptotics.CFSGSolubleFullContainerCover
