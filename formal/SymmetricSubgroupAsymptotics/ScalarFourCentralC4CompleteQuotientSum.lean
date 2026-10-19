import SymmetricSubgroupAsymptotics.ScalarFourCentralC4RawSummedCount
import SymmetricSubgroupAsymptotics.BinaryTargetRankTailSum
import SymmetricSubgroupAsymptotics.GrowingQuotientTransferNumerics

/-! Every literal original normal denominator is summed, using the proved
structural quotient dichotomy. No normal census or automorphism division is
inserted into the complete raw quotient-map convention. -/
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators
namespace SymmetricSubgroupAsymptotics.ScalarFourCentralC4TopCoordinates
open Non2UnipotentPrefixFiniteMenu
variable {Q T : Type} [Group Q] [Group T] [Finite Q] [Finite T] {c d : ℕ}

def menuColdCoefficient (T : Type) [Group T] (m : ℕ) : ℝ :=
  (Nat.card (T ≃* T) : ℝ)*((2 : ℝ)^m)^(Nat.card T)

theorem complete_quotient_sum_of_menu
    (f : T →* Equiv.Perm (Fin 3)) (hf : Function.Injective f)
    (hc : c≤3) (hd : d≤3)
    (hmenu : ∀ (N : Subgroup Q) [N.Normal],
      (∃ c' d' : ℕ, c'≤c ∧ d'≤d ∧
        Nonempty (ScalarFourCentralC4TopCoordinates (Q ⧸ N) T c' d')) ∨
      (IsPGroup 2 (Q ⧸ N) ∧ Nat.card (Q ⧸ N)≤2^7))
    (hZmud : ZmudFaithfulCharacterTupleInput) (lit : PreE7CharacterLiterature)
    (m : ℕ) (hQ : Nat.card Q≤2^m) (b : ℕ) :
    (∑ J : Subgroup (Equiv.Perm (Fin b)), completeQuotientWeight (R := Q) J) ≤
      (Nat.card {N : Subgroup Q // N.Normal} : ℝ)*
        (MarkedC4KernelRankTailNumerics.raw 1 (m+Nat.card T) b+
          BinaryKernelRankTailNumerics.raw 1 7 b+
          (subgroupCount b : ℝ)*(menuColdCoefficient T m*(2 : ℝ)^(coldSlope*b)+
            (2 : ℝ)^((357/200 : ℝ)*(b : ℝ)))) := by
  have hN (N : {N : Subgroup Q // N.Normal}) :
      (∑ J : Subgroup (Equiv.Perm (Fin b)),
        (Nat.card (GroupEpimorphism J (Q ⧸ N.val)) : ℝ)) ≤
      MarkedC4KernelRankTailNumerics.raw 1 (m+Nat.card T) b+
          BinaryKernelRankTailNumerics.raw 1 7 b+
        (subgroupCount b : ℝ)*(menuColdCoefficient T m*(2 : ℝ)^(coldSlope*b)+
          (2 : ℝ)^((357/200 : ℝ)*(b : ℝ))) := by
    letI : N.val.Normal := N.property
    have horder : Nat.card (Q ⧸ N.val)≤2^m :=
      (Nat.card_le_card_of_surjective _ (QuotientGroup.mk'_surjective N.val)).trans hQ
    rcases hmenu N.val with hret | hbin
    · obtain ⟨c',d',hc',hd',⟨E⟩⟩ := hret
      have hraw := E.raw_summed_count (hc'.trans hc) (hd'.trans hd) f hf hZmud lit m horder b
      have hcoef : E.coldCoefficient ≤ menuColdCoefficient T m := by
        unfold coldCoefficient menuColdCoefficient
        rw [Nat.cast_pow]
        exact mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (by positivity) (by exact_mod_cast horder) (Nat.card T)) (by positivity)
      have hraw' :
          (∑ J : Subgroup (Equiv.Perm (Fin b)), (Nat.card (GroupEpimorphism J (Q ⧸ N.val)) : ℝ)) ≤
          MarkedC4KernelRankTailNumerics.raw 1 (m+Nat.card T) b+
            (subgroupCount b : ℝ)*(E.coldCoefficient*(2 : ℝ)^(coldSlope*b)) := hraw
      have hh : (subgroupCount b : ℝ)*(E.coldCoefficient*(2 : ℝ)^(coldSlope*b))≤
          (subgroupCount b : ℝ)*(menuColdCoefficient T m*(2 : ℝ)^(coldSlope*b)+
            (2 : ℝ)^((357/200 : ℝ)*(b : ℝ))) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact (mul_le_mul_of_nonneg_right hcoef (by positivity)).trans
          (le_add_of_nonneg_right (by positivity))
      have hhot : 0≤BinaryKernelRankTailNumerics.raw 1 7 b := by
        unfold BinaryKernelRankTailNumerics.raw; positivity
      exact hraw'.trans (by linarith)
    · obtain ⟨hbin,hcard⟩ := hbin
      obtain ⟨r,he⟩ := hbin.exists_card_eq
      have hr : r≤7 := (Nat.pow_le_pow_iff_right (by decide : 1<2)).mp (he ▸ hcard)
      have hs := BinaryTargetRankTailSum.full_sum_le 7 r hr he b
      have ha : 0≤(subgroupCount b : ℝ)*
          (menuColdCoefficient T m*(2 : ℝ)^(coldSlope*b)) := by
        unfold menuColdCoefficient; positivity
      have hm : 0≤MarkedC4KernelRankTailNumerics.raw 1 (m+Nat.card T) b := by
        unfold MarkedC4KernelRankTailNumerics.raw markedC4Moment; positivity
      have hs' : (∑ J : Subgroup (Equiv.Perm (Fin b)),
          (Nat.card (GroupEpimorphism J (Q ⧸ N.val)) : ℝ))≤
          BinaryKernelRankTailNumerics.raw 1 7 b+
            (subgroupCount b : ℝ)*(2 : ℝ)^((357/200 : ℝ)*(b : ℝ)) := by
        convert hs using 1 <;> norm_num
      exact hs'.trans (by nlinarith)
  have htotal :
      (∑ N : {N : Subgroup Q // N.Normal},
        ∑ J : Subgroup (Equiv.Perm (Fin b)), (Nat.card (GroupEpimorphism J (Q ⧸ N.val)) : ℝ)) ≤
      (Nat.card {N : Subgroup Q // N.Normal} : ℝ)*
        (MarkedC4KernelRankTailNumerics.raw 1 (m+Nat.card T) b+
          BinaryKernelRankTailNumerics.raw 1 7 b+
          (subgroupCount b : ℝ)*(menuColdCoefficient T m*(2 : ℝ)^(coldSlope*b)+
            (2 : ℝ)^((357/200 : ℝ)*(b : ℝ)))) := by
    calc
      _ ≤ ∑ _N : {N : Subgroup Q // N.Normal},
          (MarkedC4KernelRankTailNumerics.raw 1 (m+Nat.card T) b+
          BinaryKernelRankTailNumerics.raw 1 7 b+
            (subgroupCount b : ℝ)*(menuColdCoefficient T m*(2 : ℝ)^(coldSlope*b)+
              (2 : ℝ)^((357/200 : ℝ)*(b : ℝ)))) := Finset.sum_le_sum (fun N _ => hN N)
      _ = _ := by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Fintype.card_eq_nat_card]
  unfold completeQuotientWeight completeQuotientCount
  simp only [Nat.cast_sum]
  rw [Finset.sum_comm]
  calc
    _ = ∑ N : {N : Subgroup Q // N.Normal},
        ∑ J : Subgroup (Equiv.Perm (Fin b)), (Nat.card (GroupEpimorphism J (Q ⧸ N.val)) : ℝ) := by
      apply Finset.sum_congr
      · ext N; simp
      · intro N _; rfl
    _ ≤ _ := htotal

end SymmetricSubgroupAsymptotics.ScalarFourCentralC4TopCoordinates
