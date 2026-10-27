import Mathlib.Data.Nat.Digits.Lemmas
import Mathlib.Data.List.GetD

/-! Exact digit extraction from any bounded literal coefficient list.
Every coefficient is below B, including lower/off-target coefficients.
Leading zeroes are permitted; no canonical digit-list hypothesis is used. -/
set_option autoImplicit false
namespace SymmetricSubgroupAsymptotics.NatNoCarryDigitExtraction

private theorem head_drop (l : List ℕ) (i : ℕ) :
    (l.drop i).head! = l.getD i 0 := by
  induction i generalizing l with
  | zero => cases l <;> rfl
  | succ i ih =>
    cases l with
    | nil => rfl
    | cons a l => simpa using ih l

theorem getD_lt_base (B : ℕ) (hB : 0 < B) (l : List ℕ)
    (hcoeff : ∀ a ∈ l, a < B) (i : ℕ) : l.getD i 0 < B := by
  induction l generalizing i with
  | nil => simpa using hB
  | cons a l ih =>
    cases i with
    | zero => exact hcoeff a List.mem_cons_self
    | succ i =>
      simpa using ih (fun x hx => hcoeff x (List.mem_cons_of_mem a hx)) i

theorem digit_of_ofDigits (B : ℕ) (hB : 0 < B) (l : List ℕ)
    (hcoeff : ∀ a ∈ l, a < B) (i : ℕ) :
    (Nat.ofDigits B l / B^i) % B = l.getD i 0 := by
  rw [Nat.ofDigits_div_pow_eq_ofDigits_drop i hB l hcoeff,
    Nat.ofDigits_mod_eq_head!,head_drop,
    Nat.mod_eq_of_lt (getD_lt_base B hB l hcoeff i)]

end SymmetricSubgroupAsymptotics.NatNoCarryDigitExtraction
