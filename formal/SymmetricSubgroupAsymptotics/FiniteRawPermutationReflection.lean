import SymmetricSubgroupAsymptotics.FiniteListBooleanReflection
import SymmetricSubgroupAsymptotics.SignedPermutationWordPointEncoding

/-! Literal raw forward/inverse tables produce genuine finite permutations
only after checked inverse laws. Raw Boolean word checks retain the existing
signed-word typed shadow. No group order or model recognition is assumed. -/
set_option autoImplicit false
namespace SymmetricSubgroupAsymptotics.FiniteRawPermutationReflection
open SignedPermutationWordPointEvaluation

structure Valid (n : ℕ) (forward inverse : ℕ → ℕ) : Prop where
  forward_lt : ∀ i, i < n → forward i < n
  inverse_lt : ∀ i, i < n → inverse i < n
  left_inv : ∀ i, i < n → inverse (forward i) = i
  right_inv : ∀ i, i < n → forward (inverse i) = i

def inverseCheck (n : ℕ) (forward inverse : ℕ → ℕ) : Bool :=
  (List.range n).all fun i =>
    (decide (forward i < n) && decide (inverse i < n)) &&
      (decide (inverse (forward i) = i) && decide (forward (inverse i) = i))

theorem valid_of_inverseCheck {n : ℕ} {forward inverse : ℕ → ℕ}
    (h : inverseCheck n forward inverse = true) : Valid n forward inverse := by
  have hi : ∀ i, i < n →
      (forward i < n ∧ inverse i < n) ∧
        (inverse (forward i) = i ∧ forward (inverse i) = i) := by
    intro i hin
    have hm := FiniteListBooleanReflection.all_true_at _ _ h i (List.mem_range.mpr hin)
    simpa only [Bool.and_eq_true, decide_eq_true_eq] using hm
  exact ⟨fun i h => (hi i h).1.1, fun i h => (hi i h).1.2,
    fun i h => (hi i h).2.1, fun i h => (hi i h).2.2⟩

def permutation {n : ℕ} {forward inverse : ℕ → ℕ}
    (h : Valid n forward inverse) : Equiv.Perm (Fin n) where
  toFun i := ⟨forward i.val, h.forward_lt i.val i.isLt⟩
  invFun i := ⟨inverse i.val, h.inverse_lt i.val i.isLt⟩
  left_inv i := Fin.ext (h.left_inv i.val i.isLt)
  right_inv i := Fin.ext (h.right_inv i.val i.isLt)

@[simp] theorem permutation_apply_val {n : ℕ} {forward inverse : ℕ → ℕ}
    (h : Valid n forward inverse) (i : Fin n) :
    (permutation h i).val = forward i.val := rfl

@[simp] theorem permutation_symm_apply_val {n : ℕ} {forward inverse : ℕ → ℕ}
    (h : Valid n forward inverse) (i : Fin n) :
    ((permutation h).symm i).val = inverse i.val := rfl

theorem word_encoding {n : ℕ} {af ai bf bi : ℕ → ℕ}
    (ha : Valid n af ai) (hb : Valid n bf bi) (w : List Letter) (p : Fin n) :
    applyWord af ai bf bi w p.val =
      (eval (permutation ha) (permutation hb) w p).val := by
  have hs := SignedPermutationWordPointEncoding.applyWord_encoding
    (fun i : Fin n => i.val)
    (fun i => permutation ha i) (fun i => (permutation ha).symm i)
    (fun i => permutation hb i) (fun i => (permutation hb).symm i)
    af ai bf bi (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) w p
  exact hs.trans (congrArg (fun i : Fin n => i.val) (applyWord_eq (permutation ha) (permutation hb) w p))

def wordCheck (n : ℕ) (af ai bf bi : ℕ → ℕ) (w : List Letter) : Bool :=
  (List.range n).all fun p => decide (applyWord af ai bf bi w p = p)

theorem eval_eq_one_of_wordCheck {n : ℕ} {af ai bf bi : ℕ → ℕ}
    (ha : Valid n af ai) (hb : Valid n bf bi) (w : List Letter)
    (h : wordCheck n af ai bf bi w = true) :
    eval (permutation ha) (permutation hb) w = 1 := by
  apply Equiv.ext
  intro p
  apply Fin.ext
  change (eval (permutation ha) (permutation hb) w p).val = p.val
  have hr := FiniteListBooleanReflection.all_true_at _ _ h p.val (List.mem_range.mpr p.isLt)
  have he : applyWord af ai bf bi w p.val = p.val := of_decide_eq_true hr
  exact (word_encoding ha hb w p).symm.trans he

end SymmetricSubgroupAsymptotics.FiniteRawPermutationReflection
