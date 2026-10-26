import SymmetricSubgroupAsymptotics.RegularAffineFrattiniClassBound
import SymmetricSubgroupAsymptotics.PrimitiveTopSmallFibreClassBudget

/-! Native small-fibre bounds for bare regular prime-group tops.
The original subgroup, quotient action and non-split kernel are kept.
Degree eight here pays binary fibres only; a true primitive degree-eight
ternary branch remains available separately from the existing theorem. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.RegularAffineFrattiniTopSmallFibreClassBound
open OriginalBlockClassBound RegularAffineFrattiniClassBound

theorem budget_ge_eleven (n : ℕ) : 11≤classBudget n := by
  unfold classBudget
  split_ifs <;> decide

theorem binary_unsigned_capacity (n : ℕ)
    (hn : n=8 ∨ n=16 ∨ n=27 ∨ n=32 ∨ n=64) :
    ((classBudget n+1)*2^(n-2))^3≤5^(2*n-1) := by
  rcases hn with rfl|rfl|rfl|rfl|rfl <;> unfold classBudget <;> decide +kernel

theorem ternary_capacity (n : ℕ) (hn : n=16 ∨ n=27 ∨ n=32 ∨ n=64) :
    (3^n*classBudget n)^3≤5^(3*n-1) := by
  rcases hn with rfl|rfl|rfl|rfl <;> unfold classBudget <;> decide +kernel

theorem subnormal_class_cube_le_at_original_degree
    {A Ω X : Type} [Group A] [MulAction A Ω] [MulAction A X]
    [Finite A] [Finite Ω] [Finite X] [FaithfulSMul A Ω]
    (π : Ω → X) (hπ : ∀ (g : A) (ω : Ω), π (g • ω)=g • π ω)
    (c : ℕ) (hc : c=2 ∨ c=3)
    (hsize : ∀ x, Nat.card (originalBlockFibre π x)=c)
    (P : PrimitiveAffineProfile (Top (A:=A) (X:=X)) X)
    (hselected : Nat.card X=16 ∨ Nat.card X=27 ∨ Nat.card X=32 ∨
      Nat.card X=64 ∨ (Nat.card X=8 ∧ c=2))
    (H : Subgroup A) (hH : H.IsSubnormal) :
    Nat.card (ConjClasses H)^3≤5^(Nat.card Ω-1) := by
  have hn : 5≤Nat.card X := by rcases hselected with h|h|h|h|⟨h,_⟩ <;> omega
  have hdegree : Nat.card X=8 ∨ Nat.card X=16 ∨ Nat.card X=27 ∨
      Nat.card X=32 ∨ Nat.card X=64 := by
    rcases hselected with h|h|h|h|⟨h,_⟩
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr h)))
    · exact Or.inl h
  letI : Nonempty X := Finite.card_pos_iff.mp (by omega)
  let x₀ : X := Classical.arbitrary X
  have htop : ∀ L : Subgroup (Top (A:=A) (X:=X)), L.IsSubnormal →
      Nat.card (ConjClasses L)≤classBudget (Nat.card X) :=
    fun L _ => RegularAffineFrattiniClassBound.subgroup_class_card_le P x₀ hdegree L
  rcases hc with rfl|rfl
  · have hns : ∀ a : A, ¬ (topMap (A:=A) (X:=X) a).IsSwap := by
      intro a
      exact RegularNormalActionNoSwap.not_isSwap P hn
        ((topMap (A:=A) (X:=X)).rangeRestrict a)
    have hb := BinaryBlockUnsignedGeneralClassReserve.subnormal_class_card_le_class_budget_add_one_mul
      π hπ (fun x => (hsize x).le) (by omega) (classBudget (Nat.card X))
      (budget_ge_eleven _) htop hns H hH
    have hh := (Nat.pow_le_pow_left hb 3).trans (binary_unsigned_capacity _ hdegree)
    have hcard := GaronziMarotiLargeBlockReduction.card_eq_blocks_mul_fibre π 2 hsize
    simpa only [hcard,Nat.mul_comm (Nat.card X) 2] using hh
  · have hlarge : Nat.card X=16 ∨ Nat.card X=27 ∨ Nat.card X=32 ∨ Nat.card X=64 := by
      rcases hselected with h|h|h|h|⟨_,hbad⟩
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inr (Or.inr (Or.inr h))
      · omega
    have hlocal : ∀ x (L : Subgroup (Equiv.Perm (originalBlockFibre π x))),
        Nat.card (ConjClasses L)≤3 := fun x L =>
      SmallPermutationClassBudgets.subgroup_class_card_le_three (hsize x).le L
    have hb := SubnormalSmallFibreTopClassBound.subnormal_class_card_le_power_mul_top_budget
      π hπ 3 hlocal (classBudget (Nat.card X)) htop H hH
    have hh := (Nat.pow_le_pow_left hb 3).trans (ternary_capacity _ hlarge)
    have hcard := GaronziMarotiLargeBlockReduction.card_eq_blocks_mul_fibre π 3 hsize
    simpa only [hcard,Nat.mul_comm (Nat.card X) 3] using hh

end SymmetricSubgroupAsymptotics.RegularAffineFrattiniTopSmallFibreClassBound
