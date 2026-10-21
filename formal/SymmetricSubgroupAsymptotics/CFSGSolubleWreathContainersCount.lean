import SymmetricSubgroupAsymptotics.CFSGSolubleWreathContainersStepMenu
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic.Linarith

/-! A fixed polynomial logarithmic budget closes the actual wreath-menu
recurrence. Only elementary tuple counting and integer arithmetic enter. -/
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators
namespace SymmetricSubgroupAsymptotics.CFSGSolubleWreathContainers
open CFSGSolublePrimitiveContainers

def logBudget (n : ℕ) : ℕ := (logSize n + 1) ^ 4
def containerBudget (n : ℕ) : ℕ := 32 * n * logBudget n

theorem logSize_mono {m n : ℕ} (h : m ≤ n) : logSize m ≤ logSize n := by
  unfold logSize
  rw [Nat.log2_eq_log_two, Nat.log2_eq_log_two]
  exact Nat.add_le_add_right (Nat.log_mono_right h) 1

theorem logBudget_mono {m n : ℕ} (h : m ≤ n) : logBudget m ≤ logBudget n :=
  Nat.pow_le_pow_left (Nat.add_le_add_right (logSize_mono h) 1) 4

theorem logBudget_pos (n : ℕ) : 0 < logBudget n := by unfold logBudget; positivity

theorem logSize_le_logBudget (n : ℕ) : logSize n ≤ logBudget n :=
  (Nat.le_succ _).trans (Nat.le_self_pow (by decide : (4 : ℕ) ≠ 0) _)

theorem factorial_le_two_pow (n : ℕ) : n.factorial ≤ 2 ^ (n * logSize n) := by
  calc
    n.factorial ≤ n ^ n := n.factorial_le_pow
    _ ≤ (2 ^ logSize n) ^ n := Nat.pow_le_pow_left (card_le_two_pow_logSize n) n
    _ = _ := by rw [← pow_mul, Nat.mul_comm]

theorem primitiveIndex_card_le_budget (n : ℕ) (hn : 1 ≤ n) :
    Nat.card (PrimitiveIndex n) ≤ 2 ^ (4 * n * logBudget n) := by
  have hp : n + 1 ≤ 2 ^ n := Nat.succ_le_of_lt n.lt_two_pow_self
  have hl : logSize n ≤ 2 ^ n := by
    unfold logSize
    rw [Nat.log2_eq_log_two]
    exact (Nat.add_le_add_right (Nat.log_le_self 2 n) 1).trans hp
  have hf := factorial_le_two_pow n
  have hfour : logSize n ^ 4 ≤ logBudget n :=
    Nat.pow_le_pow_left (Nat.le_succ _) 4
  have hbase := primitiveIndex_card_le n
  have hexp : n + n + logBudget n + n * logSize n ≤ 4 * n * logBudget n := by
    have hb : 1 ≤ logBudget n := logBudget_pos n
    have h1 := Nat.mul_le_mul_right (logBudget n) hn
    have h2 := Nat.mul_le_mul_left n (logSize_le_logBudget n)
    have h3 := Nat.mul_le_mul_left (2 * n) hb
    nlinarith
  calc
    Nat.card (PrimitiveIndex n) ≤
        (n + 1) * logSize n * (2 ^ (logSize n ^ 4) * n.factorial) := hbase
    _ ≤ (2 ^ n * 2 ^ n) * (2 ^ logBudget n * 2 ^ (n * logSize n)) :=
      Nat.mul_le_mul (Nat.mul_le_mul hp hl)
        (Nat.mul_le_mul (Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) hfour) hf)
    _ = 2 ^ (n + n + logBudget n + n * logSize n) := by
      rw [← pow_add, ← pow_add, ← pow_add]
      congr 1
      omega
    _ ≤ _ := Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) hexp

theorem factorPair_card_le (n : ℕ) : Nat.card (FactorPair n) ≤ n * n := by
  have h := Nat.card_le_card_of_injective
    (Subtype.val : FactorPair n → Fin n × Fin n) Subtype.val_injective
  simpa only [Nat.card_prod, Nat.card_fin] using h

theorem stepIndex_card_le_budget (n : ℕ) (hn : 2 ≤ n)
    (below : ∀ d : Fin n, TransitiveSolubleContainerCover d.val)
    (hbelow : ∀ d : Fin n, Nat.card (below d).Index ≤ 2 ^ containerBudget d.val) :
    Nat.card (StepIndex n below) ≤ 2 ^ containerBudget n := by
  let B := logBudget n
  have hB : 1 ≤ B := logBudget_pos n
  have hNB : 1 ≤ n * B := Nat.mul_pos (by omega) (by omega)
  have hpair (p : FactorPair n) :
      Nat.card (PrimitiveIndex p.val.1.val) * Nat.card (below p.val.2).Index ≤
        2 ^ (18 * n * B) := by
    let r := p.val.1.val
    let s := p.val.2.val
    have hr : 2 ≤ r := p.property.1
    have hs : 2 ≤ s := p.property.2.1
    have hrs : r * s = n := p.property.2.2
    have hrn : r ≤ n := p.val.1.isLt.le
    have hsn : s ≤ n := p.val.2.isLt.le
    have htwoR : 2 * r ≤ n := by nlinarith
    have htwoS : 2 * s ≤ n := by nlinarith
    have hP := primitiveIndex_card_le_budget r (by omega)
    have hT := hbelow p.val.2
    have hPr : 4 * r * logBudget r ≤ 4 * r * B :=
      Nat.mul_le_mul_left _ (logBudget_mono hrn)
    have hTs : containerBudget s ≤ 32 * s * B :=
      Nat.mul_le_mul_left _ (logBudget_mono hsn)
    have he : 4 * r * B + 32 * s * B ≤ 18 * n * B := by
      have h := Nat.mul_le_mul_right B (show 4 * r + 32 * s ≤ 18 * n by omega)
      nlinarith
    calc
      _ ≤ 2 ^ (4 * r * logBudget r) * 2 ^ containerBudget s := Nat.mul_le_mul hP hT
      _ ≤ 2 ^ (4 * r * B) * 2 ^ (32 * s * B) :=
        Nat.mul_le_mul (Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) hPr)
          (Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) hTs)
      _ = 2 ^ (4 * r * B + 32 * s * B) := (pow_add _ _ _).symm
      _ ≤ _ := Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) he
  have hcount : Nat.card (FactorPair n) ≤ 2 ^ (2 * n) := by
    calc
      _ ≤ n * n := factorPair_card_le n
      _ ≤ 2 ^ n * 2 ^ n := Nat.mul_le_mul n.lt_two_pow_self.le n.lt_two_pow_self.le
      _ = _ := by rw [← pow_add]; congr 1; omega
  have hsum : (∑ p : FactorPair n,
      Nat.card (PrimitiveIndex p.val.1.val) * Nat.card (below p.val.2).Index) ≤
        2 ^ (20 * n * B) := by
    calc
      _ ≤ ∑ _p : FactorPair n, 2 ^ (18 * n * B) := Finset.sum_le_sum (fun p _ => hpair p)
      _ = Nat.card (FactorPair n) * 2 ^ (18 * n * B) := by
        simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul,
          ← Nat.card_eq_fintype_card]
      _ ≤ 2 ^ (2 * n) * 2 ^ (18 * n * B) := Nat.mul_le_mul_right _ hcount
      _ = 2 ^ (2 * n + 18 * n * B) := (pow_add _ _ _).symm
      _ ≤ _ := Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) (by
        have h := Nat.mul_le_mul_left (2 * n) hB
        nlinarith)
  have hprim : Nat.card (PrimitiveIndex n) ≤ 2 ^ (20 * n * B) :=
    (primitiveIndex_card_le_budget n (by omega)).trans
      (Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) (by dsimp [B]; nlinarith))
  have hfac : n.factorial ≤ 2 ^ (n * B) :=
    (factorial_le_two_pow n).trans (Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ))
      (Nat.mul_le_mul_left n (logSize_le_logBudget n)))
  rw [stepIndex_card_eq]
  calc
    _ ≤ (2 ^ (20 * n * B) + 2 ^ (20 * n * B)) * 2 ^ (n * B) :=
      Nat.mul_le_mul (Nat.add_le_add hprim hsum) hfac
    _ = 2 ^ (21 * n * B + 1) := by
      rw [← two_mul, ← pow_succ', ← pow_add]
      congr 1
      ring
    _ ≤ 2 ^ containerBudget n := Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) (by
      unfold containerBudget
      change 21 * n * B + 1 ≤ 32 * n * B
      nlinarith)

end SymmetricSubgroupAsymptotics.CFSGSolubleWreathContainers
