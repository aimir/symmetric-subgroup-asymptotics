import SymmetricSubgroupAsymptotics.MarkedC4ActualBinaryWordSkeletons

/-! A once-global finite alphabet for the literal shapes and original
permutation letters. Its cardinal is polynomial times a cutoff-constant
power of the physical degree; no subgroup image is counted in this menu. -/
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators
namespace SymmetricSubgroupAsymptotics.MarkedC4.ActualBinarySkeletonMenu
open FiniteOrbitWordShapes FiniteBinaryWordTargets ActualBinaryWordSkeletons

def letterBound (C : ℕ) : ℕ := 2^C.factorial

theorem letter_card_le (C : ℕ) (d : Fin C) :
    Nat.card (Subgroup (Equiv.Perm (Fin d.val)))≤letterBound C := by
  have hh := Fintype.card_le_of_injective
    (fun H : Subgroup (Equiv.Perm (Fin d.val)) => (H : Set (Equiv.Perm (Fin d.val))))
    SetLike.coe_injective
  simp only [Fintype.card_set,Fintype.card_perm,Fintype.card_fin] at hh
  exact (show Nat.card (Subgroup (Equiv.Perm (Fin d.val)))≤2^d.val.factorial by
    simpa only [Nat.card_eq_fintype_card] using hh).trans
    (pow_le_pow_right₀ (by norm_num : 1≤(2 : ℕ)) (Nat.factorial_le d.isLt.le))

theorem local_card_le {C b : ℕ} (S : Shape C b) :
    Nat.card (LocalGroups S)≤(letterBound C)^b := by
  change Nat.card (∀ i : Fin S.length.val,Subgroup (Equiv.Perm (Fin (S.degrees i).val)))≤_
  rw [Nat.card_pi]
  calc
    _ ≤ ∏ _i : Fin S.length.val,letterBound C :=
      Finset.prod_le_prod' (fun i _ => letter_card_le C (S.degrees i))
    _ = (letterBound C)^S.length.val := by simp
    _ ≤ _ := pow_le_pow_right₀ (by unfold letterBound; exact one_le_pow₀ (by norm_num : 1≤(2 : ℕ))) (Nat.le_of_lt_succ S.length.isLt)

theorem shape_card_le (C b : ℕ) : Nat.card (Shape C b)≤(b+1)*(max C 1)^b := by
  have hi := Nat.card_le_card_of_injective (@Shape.code C b) (@Shape.code_injective C b)
  have hc : Nat.card (Σ t : Fin (b+1),Fin t.val → Fin C)≤(b+1)*(max C 1)^b := by
    rw [Nat.card_sigma]
    calc
      _ ≤ ∑ _t : Fin (b+1),(max C 1)^b := by
        apply Finset.sum_le_sum
        intro t _
        simp only [Nat.card_fun,Nat.card_fin]
        exact (Nat.pow_le_pow_left (le_max_left C 1) _).trans
          (pow_le_pow_right₀ (le_max_right C 1) (Nat.le_of_lt_succ t.isLt))
      _ = _ := by simp
  exact hi.trans hc

theorem skeleton_card_le (C b : ℕ) :
    Nat.card (Skeleton C b)≤(b+1)*(max C 1)^b*(letterBound C)^b := by
  have hi := Nat.card_le_card_of_injective
    (fun p : Skeleton C b => p.val) Subtype.val_injective
  have hc : Nat.card (Σ S : Shape C b,LocalGroups S)≤Nat.card (Shape C b)*(letterBound C)^b := by
    rw [Nat.card_sigma]
    calc
      _ ≤ ∑ _S : Shape C b,(letterBound C)^b :=
        Finset.sum_le_sum (fun S _ => local_card_le S)
      _ = _ := by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Nat.card_eq_fintype_card,Nat.cast_id]
  exact (hi.trans hc).trans (Nat.mul_le_mul_right _ (shape_card_le C b))

end SymmetricSubgroupAsymptotics.MarkedC4.ActualBinarySkeletonMenu
