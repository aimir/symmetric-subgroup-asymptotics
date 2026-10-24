import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic.Ring

/-! Uniform level-set bounds for literal binary quadratic forms.
The cross coefficient is nonzero and the level is nonzero. No conic
classification, splitting-field choice, characteristic restriction,
or enumeration of the coefficient field is used. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical BigOperators
namespace SymmetricSubgroupAsymptotics.BinaryQuadraticLevelCardinality

variable {K : Type*} [Field K]

def eval (a b c : K) (v : K × K) : K := a * v.1 ^ 2 + b * v.1 * v.2 + c * v.2 ^ 2

theorem quadratic_fibre_card_le_two (a b c t : K) (ha : a ≠ 0) :
    Nat.card {y : K // a * y ^ 2 + b * y + c = t} ≤ 2 := by
  by_cases hE : Nonempty {y : K // a * y ^ 2 + b * y + c = t}
  · obtain ⟨u⟩ := hE
    have hcase (y : {y : K // a * y ^ 2 + b * y + c = t}) :
        y.val = u.val ∨ y.val = (-b) / a - u.val := by
      have he : (y.val - u.val) * (a * (y.val + u.val) + b) = 0 := by
        calc
          _ = (a * y.val ^ 2 + b * y.val + c) -
              (a * u.val ^ 2 + b * u.val + c) := by ring
          _ = 0 := by rw [y.property, u.property, sub_self]
      rcases mul_eq_zero.mp he with h | h
      · exact Or.inl (sub_eq_zero.mp h)
      · apply Or.inr
        have hs : y.val + u.val = (-b) / a :=
          (eq_div_iff ha).2 (by simpa only [mul_comm] using eq_neg_of_add_eq_zero_left h)
        exact eq_sub_iff_add_eq.mpr hs
    let code : {y : K // a * y ^ 2 + b * y + c = t} → Bool :=
      fun y => decide (y.val = u.val)
    have hinj : Function.Injective code := by
      intro y z he
      apply Subtype.ext
      change decide (y.val = u.val) = decide (z.val = u.val) at he
      have hi : y.val = u.val ↔ z.val = u.val := decide_eq_decide.mp he
      by_cases hy : y.val = u.val
      · exact hy.trans (hi.mp hy).symm
      · have hz : z.val ≠ u.val := fun hz => hy (hi.mpr hz)
        exact ((hcase y).resolve_left hy).trans ((hcase z).resolve_left hz).symm
    calc
      _ ≤ Nat.card Bool := Nat.card_le_card_of_injective code hinj
      _ = 2 := by simp only [Nat.card_eq_fintype_card, Fintype.card_bool]
  · letI : IsEmpty {y : K // a * y ^ 2 + b * y + c = t} := ⟨fun y => hE ⟨y⟩⟩
    simp only [Nat.card_of_isEmpty, Nat.zero_le]

theorem fixed_first_fibre_card_le_two [Finite K] (a b c t x : K) (hb : b ≠ 0) (ht : t ≠ 0) :
    Nat.card {y : K // eval a b c (x, y) = t} ≤ 2 := by
  by_cases hc : c = 0
  · by_cases hx : x = 0
    · letI : IsEmpty {y : K // eval a b c (x, y) = t} :=
        ⟨fun y => ht (by simpa only [eval, hx, hc, zero_pow (by decide : 2 ≠ 0),
          mul_zero, zero_mul, zero_add] using y.property.symm)⟩
      simp only [Nat.card_of_isEmpty, Nat.zero_le]
    · let code : {y : K // eval a b c (x, y) = t} → Fin 1 := fun _ => 0
      have hinj : Function.Injective code := by
        intro y z _
        have he : a * x ^ 2 + (b * x) * y.val = a * x ^ 2 + (b * x) * z.val := by
          simpa only [eval, hc, zero_mul, add_zero] using y.property.trans z.property.symm
        exact Subtype.ext (mul_left_cancel₀ (mul_ne_zero hb hx) (add_left_cancel he))
      calc
        _ ≤ 1 := by simpa only [Nat.card_fin] using Nat.card_le_card_of_injective code hinj
        _ ≤ 2 := by decide
  · let encode : {y : K // eval a b c (x, y) = t} →
        {y : K // c * y ^ 2 + (b * x) * y + a * x ^ 2 = t} := fun y =>
      ⟨y.val, by
        calc
          _ = eval a b c (x, y.val) := by unfold eval; ring
          _ = t := y.property⟩
    have hinj : Function.Injective encode := by
      intro y z he
      exact Subtype.ext (congrArg
        (fun w : {y : K // c * y ^ 2 + (b * x) * y + a * x ^ 2 = t} => w.val) he)
    exact (Nat.card_le_card_of_injective encode hinj).trans
      (quadratic_fibre_card_le_two c (b * x) (a * x ^ 2) t hc)

theorem level_card_le_two_mul_card [Finite K] (a b c t : K) (hb : b ≠ 0) (ht : t ≠ 0) :
    Nat.card {v : K × K // eval a b c v = t} ≤ 2 * Nat.card K := by
  letI : Fintype K := Fintype.ofFinite K
  let e : {v : K × K // eval a b c v = t} ≃
      Σ x : K, {y : K // eval a b c (x, y) = t} := {
    toFun := fun v => ⟨v.val.1, ⟨v.val.2, v.property⟩⟩
    invFun := fun v => ⟨(v.1, v.2.val), v.2.property⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
  calc
    _ = Nat.card (Σ x : K, {y : K // eval a b c (x, y) = t}) := Nat.card_congr e
    _ = ∑ x : K, Nat.card {y : K // eval a b c (x, y) = t} := Nat.card_sigma
    _ ≤ ∑ _x : K, 2 := Finset.sum_le_sum (fun x _ => fixed_first_fibre_card_le_two a b c t x hb ht)
    _ = 2 * Nat.card K := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
        Nat.card_eq_fintype_card, Nat.cast_id, Nat.mul_comm]

end SymmetricSubgroupAsymptotics.BinaryQuadraticLevelCardinality
