import SymmetricSubgroupAsymptotics.ScalarFourCentralSymmetricQuotientDichotomy
import SymmetricSubgroupAsymptotics.ScalarFourCentralRawSummedCount
import SymmetricSubgroupAsymptotics.SmallBinaryRankTailSum
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
variable {Q T : Type} [Group Q] [Group T] [Finite Q] [Finite T] {c d : ℕ}
  (D : ScalarFourCentralTopCoordinates Q T c d)

def symmetricColdCoefficient (T : Type) [Group T] (m : ℕ) : ℝ :=
  (Nat.card (T ≃* T) : ℝ)*((2 : ℝ)^m)^6

private theorem symmetric_card (e : T ≃* Equiv.Perm (Fin 3)) : Nat.card T=6 := by
  rw [Nat.card_congr e.toEquiv,Nat.card_perm,Nat.card_fin]
  norm_num

private theorem symmetric_raw_four_le (m b : ℕ) :
    BinaryKernelRankTailNumerics.raw 1 4 b≤BinaryKernelRankTailNumerics.raw 1 (m+6) b := by
  unfold BinaryKernelRankTailNumerics.raw
  simp only [one_mul]
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  have hn : 1≤b.factorial := Nat.succ_le_iff.mpr (Nat.factorial_pos b)
  exact pow_le_pow_right₀ (by exact_mod_cast hn) (by omega)

theorem symmetric_complete_quotient_summed_count
    (e : T ≃* Equiv.Perm (Fin 3))
    (hc : c≤3) (hd : d≤3) (hcubic : orderOf D.cubic=3)
    (hZmud : ZmudFaithfulCharacterTupleInput) (lit : PreE7CharacterLiterature)
    (m : ℕ) (hQ : Nat.card Q≤2^m) (b : ℕ) :
    (∑ J : Subgroup (Equiv.Perm (Fin b)), completeQuotientWeight (R := Q) J) ≤
      (Nat.card {N : Subgroup Q // N.Normal} : ℝ)*
        (BinaryKernelRankTailNumerics.raw 1 (m+6) b+
          (subgroupCount b : ℝ)*(symmetricColdCoefficient T m*(2 : ℝ)^(coldSlope*b)+
            (2 : ℝ)^((51/50 : ℝ)*(b : ℝ)))) := by
  have hN (N : {N : Subgroup Q // N.Normal}) :
      (∑ J : Subgroup (Equiv.Perm (Fin b)),
        (Nat.card (GroupEpimorphism J (Q ⧸ N.val)) : ℝ)) ≤
      BinaryKernelRankTailNumerics.raw 1 (m+6) b+
        (subgroupCount b : ℝ)*(symmetricColdCoefficient T m*(2 : ℝ)^(coldSlope*b)+
          (2 : ℝ)^((51/50 : ℝ)*(b : ℝ))) := by
    letI : N.val.Normal := N.property
    have horder : Nat.card (Q ⧸ N.val)≤2^m :=
      (Nat.card_le_card_of_surjective _ (QuotientGroup.mk'_surjective N.val)).trans hQ
    rcases D.symmetric_all_original_quotients e hcubic N.val with hret | hbin
    · obtain ⟨c',d',hc',hd',⟨E⟩⟩ := hret
      have hraw := E.raw_summed_count (hc'.trans hc) (hd'.trans hd) e.toMonoidHom e.injective hZmud lit m horder b
      have hcoef : E.coldCoefficient ≤ symmetricColdCoefficient T m := by
        unfold coldCoefficient symmetricColdCoefficient
        rw [symmetric_card e,Nat.cast_mul,Nat.cast_pow]
        exact mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (by positivity) (by exact_mod_cast horder) 6) (by positivity)
      have hraw' :
          (∑ J : Subgroup (Equiv.Perm (Fin b)), (Nat.card (GroupEpimorphism J (Q ⧸ N.val)) : ℝ)) ≤
          BinaryKernelRankTailNumerics.raw 1 (m+6) b+
            (subgroupCount b : ℝ)*(E.coldCoefficient*(2 : ℝ)^(coldSlope*b)) := by
        simpa only [symmetric_card e,BinaryKernelRankTailNumerics.raw,one_mul] using hraw
      apply hraw'.trans
      apply add_le_add_right
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact (mul_le_mul_of_nonneg_right hcoef (by positivity)).trans
        (le_add_of_nonneg_right (by positivity))
    · obtain ⟨hbin,hcard⟩ := hbin
      obtain ⟨r,he⟩ := hbin.exists_card_eq
      have hcard4 : Nat.card (Q ⧸ N.val)≤2^4 :=
        hcard.trans (Nat.pow_le_pow_right (by decide : 1≤2) (by omega))
      have hr : r≤4 := (Nat.pow_le_pow_iff_right (by decide : 1<2)).mp (he ▸ hcard4)
      have hs := SmallBinaryRankTailSum.full_sum_le r hr he b
      have hs' := hs.trans (add_le_add (symmetric_raw_four_le m b) le_rfl)
      apply hs'.trans
      apply add_le_add_right
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact le_add_of_nonneg_left (by unfold symmetricColdCoefficient; positivity)
  have htotal :
      (∑ N : {N : Subgroup Q // N.Normal},
        ∑ J : Subgroup (Equiv.Perm (Fin b)), (Nat.card (GroupEpimorphism J (Q ⧸ N.val)) : ℝ)) ≤
      (Nat.card {N : Subgroup Q // N.Normal} : ℝ)*
        (BinaryKernelRankTailNumerics.raw 1 (m+6) b+
          (subgroupCount b : ℝ)*(symmetricColdCoefficient T m*(2 : ℝ)^(coldSlope*b)+
            (2 : ℝ)^((51/50 : ℝ)*(b : ℝ)))) := by
    calc
      _ ≤ ∑ _N : {N : Subgroup Q // N.Normal},
          (BinaryKernelRankTailNumerics.raw 1 (m+6) b+
            (subgroupCount b : ℝ)*(symmetricColdCoefficient T m*(2 : ℝ)^(coldSlope*b)+
              (2 : ℝ)^((51/50 : ℝ)*(b : ℝ)))) := Finset.sum_le_sum (fun N _ => hN N)
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
