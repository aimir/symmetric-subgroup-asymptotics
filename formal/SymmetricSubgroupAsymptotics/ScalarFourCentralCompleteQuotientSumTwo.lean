import SymmetricSubgroupAsymptotics.ScalarFourCentralCubicAllQuotients
import SymmetricSubgroupAsymptotics.ScalarFourCentralRawSummedCountOfCold
import SymmetricSubgroupAsymptotics.ScalarFourCentralCompleteQuotientSum
import SymmetricSubgroupAsymptotics.SmallBinaryQuotientEpiEnvelopeTwo
import SymmetricSubgroupAsymptotics.GrowingQuotientTransferNumerics
import SymmetricSubgroupAsymptotics.BinaryKernelRankTailNumerics

/-! Every literal original normal denominator is summed, using the proved
structural quotient dichotomy. No normal census or automorphism division is
inserted into the complete raw quotient-map convention. -/
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators
namespace SymmetricSubgroupAsymptotics.ScalarFourCentralTopCoordinates
open Non2UnipotentPrefixFiniteMenu
variable {Q : Type} [Group Q] [Finite Q] {c d : ℕ}
  (D : ScalarFourCentralTopCoordinates Q CyclicThree c d)

private theorem cubic_card_two : Nat.card CyclicThree=3 := by
  rw [Nat.card_congr Multiplicative.toAdd]
  simp

theorem complete_quotient_summed_count_two
    (hc : c≤2) (hd : d≤2) (hcubic : D.cubic=Multiplicative.ofAdd (1 : ZMod 3))
    (f : CyclicThree →* Equiv.Perm (Fin 3)) (hf : Function.Injective f)
    (hZmud : ZmudFaithfulCharacterTupleInput) (lit : PreE7CharacterLiterature)
    (m : ℕ) (hQ : Nat.card Q≤2^m) (b : ℕ) :
    (∑ J : Subgroup (Equiv.Perm (Fin b)), completeQuotientWeight (R := Q) J) ≤
      (Nat.card {N : Subgroup Q // N.Normal} : ℝ)*
        (BinaryKernelRankTailNumerics.raw 1 (m+3) b+
          (subgroupCount b : ℝ)*(cubicColdCoefficient m*(2 : ℝ)^(coldSlopeTwo*b)+
            (2 : ℝ)^((1 : ℝ)*(b : ℝ)))) := by
  have hN (N : {N : Subgroup Q // N.Normal}) :
      (∑ J : Subgroup (Equiv.Perm (Fin b)),
        (Nat.card (GroupEpimorphism J (Q ⧸ N.val)) : ℝ)) ≤
      BinaryKernelRankTailNumerics.raw 1 (m+3) b+
        (subgroupCount b : ℝ)*(cubicColdCoefficient m*(2 : ℝ)^(coldSlopeTwo*b)+
          (2 : ℝ)^((1 : ℝ)*(b : ℝ))) := by
    letI : N.val.Normal := N.property
    have horder : Nat.card (Q ⧸ N.val)≤2^m :=
      (Nat.card_le_card_of_surjective _ (QuotientGroup.mk'_surjective N.val)).trans hQ
    rcases D.all_original_quotients hcubic N.val with hret | hbin
    · obtain ⟨c',d',hc',hd',⟨E⟩⟩ := hret
      have hraw := E.raw_summed_count_two (hc'.trans hc) (hd'.trans hd) f hf hZmud lit m horder b
      have hcoef : E.coldCoefficient≤cubicColdCoefficient m := by
        unfold coldCoefficient cubicColdCoefficient
        rw [cubic_card_two,Nat.cast_mul,Nat.cast_pow]
        exact mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (by positivity) (by exact_mod_cast horder) 3) (by positivity)
      have hraw' :
          (∑ J : Subgroup (Equiv.Perm (Fin b)), (Nat.card (GroupEpimorphism J (Q ⧸ N.val)) : ℝ)) ≤
          BinaryKernelRankTailNumerics.raw 1 (m+3) b+
            (subgroupCount b : ℝ)*(E.coldCoefficient*(2 : ℝ)^(coldSlopeTwo*b)) := by
        simpa only [cubic_card_two,BinaryKernelRankTailNumerics.raw,one_mul] using hraw
      apply hraw'.trans
      apply add_le_add_right
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact (mul_le_mul_of_nonneg_right hcoef (by positivity)).trans
        (le_add_of_nonneg_right (by positivity))
    · obtain ⟨r,hr,⟨e⟩⟩ := hbin
      have hs :
          (∑ J : Subgroup (Equiv.Perm (Fin b)), (Nat.card (GroupEpimorphism J (Q ⧸ N.val)) : ℝ)) ≤
          (subgroupCount b : ℝ)*(2 : ℝ)^((1 : ℝ)*(b : ℝ)) := by
        calc
          _ ≤ ∑ _J : Subgroup (Equiv.Perm (Fin b)), (2 : ℝ)^((1 : ℝ)*(b : ℝ)) :=
            Finset.sum_le_sum (fun J _ => small_binary_quotient_epi_envelope_two r (hr.trans hc) e b J)
          _ = _ := by simp [subgroupCount]
      apply hs.trans
      have ha : 0≤cubicColdCoefficient m*(2 : ℝ)^(coldSlopeTwo*b) := by
        unfold cubicColdCoefficient
        positivity
      have hh : 0≤BinaryKernelRankTailNumerics.raw 1 (m+3) b := by
        unfold BinaryKernelRankTailNumerics.raw
        positivity
      nlinarith [mul_nonneg (show 0≤(subgroupCount b : ℝ) by positivity) ha]
  have htotal :
      (∑ N : {N : Subgroup Q // N.Normal},
        ∑ J : Subgroup (Equiv.Perm (Fin b)), (Nat.card (GroupEpimorphism J (Q ⧸ N.val)) : ℝ)) ≤
      (Nat.card {N : Subgroup Q // N.Normal} : ℝ)*
        (BinaryKernelRankTailNumerics.raw 1 (m+3) b+
          (subgroupCount b : ℝ)*(cubicColdCoefficient m*(2 : ℝ)^(coldSlopeTwo*b)+
            (2 : ℝ)^((1 : ℝ)*(b : ℝ)))) := by
    calc
      _ ≤ ∑ _N : {N : Subgroup Q // N.Normal},
          (BinaryKernelRankTailNumerics.raw 1 (m+3) b+
            (subgroupCount b : ℝ)*(cubicColdCoefficient m*(2 : ℝ)^(coldSlopeTwo*b)+
              (2 : ℝ)^((1 : ℝ)*(b : ℝ)))) := Finset.sum_le_sum (fun N _ => hN N)
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

end SymmetricSubgroupAsymptotics.ScalarFourCentralTopCoordinates
