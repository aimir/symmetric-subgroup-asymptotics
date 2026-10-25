import SymmetricSubgroupAsymptotics.BinarySubnormalSymmetricTopClassGap
import SymmetricSubgroupAsymptotics.FinitePartitionCompositionMenu
import SymmetricSubgroupAsymptotics.PermutationalWreathTransport

/-! The SAME actual-range geometric mean extends the binary natural
symmetric/alternating gap down to eight coordinates. Its two small seeds
use the checked partition menu at eight and finite Fibonacci convolution.
No permutation action, matrix group, or subgroup is enumerated. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped BigOperators Classical
namespace SymmetricSubgroupAsymptotics.BinarySubnormalSymmetricTopEightClassGap
open BinaryPartitionBudget WreathHomProjectionRange

variable {A C : Type} [Group A] [CommGroup C] [Finite A] [Finite C]

theorem pairedPartitions_card_le_fib_convolution (n : ℕ) :
    Nat.card (PairedPartitions n) ≤
      ∑ i : Fin (n+1), Nat.fib (i.val+1)*Nat.fib (n-i.val+1) := by
  rw [Nat.card_sigma]
  apply Finset.sum_le_sum
  intro i _
  rw [Nat.card_prod]
  exact Nat.mul_le_mul (PartitionFibonacciBound.partition_card_le_fib i.val)
    (PartitionFibonacciBound.partition_card_le_fib (n-i.val))

theorem partition_eight_card_le : Nat.card (Nat.Partition 8) ≤ 22 :=
  (FinitePartitionCompositionMenu.partition_card_le_menu_card 8).trans_eq
    FinitePartitionCompositionMenu.menu_eight_card

theorem partition_nine_card_le : Nat.card (Nat.Partition 9) ≤ 43 := by
  calc
    _ ≤ Nat.card (Nat.Partition 8)+Nat.card (Nat.Partition 7) :=
      PartitionFibonacciBound.partition_card_recurrence 9 (by decide)
    _ ≤ 22+Nat.fib 8 := Nat.add_le_add partition_eight_card_le
      (PartitionFibonacciBound.partition_card_le_fib 7)
    _ ≤ 43 := by decide

private theorem restricted_wreath_class_card_le
    (n w : ℕ) (hC : Nat.card C=2) (R : Subgroup (Equiv.Perm (Fin n)))
    (hindex : R.index ≤ 2) (hpaired : Nat.card (PairedPartitions n) ≤ w) :
    Nat.card (ConjClasses (PermutationalWreathProduct C R (Fin n))) ≤ 2*w := by
  let N := R.comap (PermutationalWreathProduct.rightHom (D := C) (I := Fin n))
  let e := WreathRestrictedTopClassBound.topPreimageEquiv (C := C) (I := Fin n) R
  have he : Nat.card (ConjClasses (PermutationalWreathProduct C R (Fin n))) ≤
      Nat.card (ConjClasses N) :=
    Nat.card_le_card_of_surjective (ConjClasses.map e.symm.toMonoidHom)
      (ConjClasses.map_surjective e.symm.surjective)
  have hi : N.index ≤ 2 :=
    (WreathRestrictedTopClassBound.topPreimage_index (C := C) (I := Fin n) R).le.trans hindex
  have hfull : Nat.card (ConjClasses
      (PermutationalWreathProduct C (Equiv.Perm (Fin n)) (Fin n))) ≤ w := by
    have h := BinaryFullWreathClassBound.class_card_le_pairedPartitions (I := Fin n) hC
    have hh : Nat.card (ConjClasses
        (PermutationalWreathProduct C (Equiv.Perm (Fin n)) (Fin n))) ≤
        Nat.card (PairedPartitions n) := by simpa only [Nat.card_fin] using h
    exact hh.trans hpaired
  exact he.trans ((ConjugacyClassSubgroupIndexBound.class_card_le_index_mul N).trans
    (Nat.mul_le_mul hi hfull))

private theorem gap_of_counts (n p w : ℕ) (hC : Nat.card C=2)
    (f : A →* PermutationalWreathProduct C (Equiv.Perm (Fin n)) (Fin n))
    (hf : Function.Injective f)
    (hclass : Nat.card (ConjClasses (topProjection f).range) ≤ p)
    (hindex : (topProjection f).range.index ≤ 2)
    (hpaired : Nat.card (PairedPartitions n) ≤ w)
    (hnum : (2^n*p*(2*w))^3 ≤ 5^(4*n-4)) :
    Nat.card (ConjClasses A)^3 ≤ 5^(2*n-2) := by
  have hsquare : Nat.card (ConjClasses A)^2 ≤ 2^n*p*(2*w) := by
    calc
      _ ≤ 2^n*Nat.card (ConjClasses (topProjection f).range)*
          Nat.card (ConjClasses (PermutationalWreathProduct C (topProjection f).range (Fin n))) := by
        simpa only [hC,Nat.card_fin] using class_square_le_actual_top_range_wreath f hf
      _ ≤ _ := Nat.mul_le_mul (Nat.mul_le_mul_left _ hclass)
        (restricted_wreath_class_card_le n w hC _ hindex hpaired)
  have hpow : (Nat.card (ConjClasses A)^3)^2 ≤ (5^(2*n-2))^2 := by
    calc
      _ = (Nat.card (ConjClasses A)^2)^3 := by ring
      _ ≤ (2^n*p*(2*w))^3 := Nat.pow_le_pow_left hsquare 3
      _ ≤ 5^(4*n-4) := hnum
      _ = (5^(2*n-2))^2 := by rw [←pow_mul]; congr 1; omega
  exact (Nat.pow_le_pow_iff_left (by decide : (2:ℕ)≠0)).mp hpow

private theorem gap_of_partition_counts (n p w : ℕ) (hn : 5 ≤ n) (hC : Nat.card C=2)
    (hpart : Nat.card (Nat.Partition n) ≤ p)
    (hpaired : Nat.card (PairedPartitions n) ≤ w)
    (hsmall : (2^(n+1))^3 ≤ 5^(2*n-2))
    (hnum : (2^n*p*(2*w))^3 ≤ 5^(4*n-4))
    (f : A →* PermutationalWreathProduct C (Equiv.Perm (Fin n)) (Fin n))
    (hf : Function.Injective f) (hR : (topProjection f).range.IsSubnormal) :
    Nat.card (ConjClasses A)^3 ≤ 5^(2*n-2) := by
  letI : Nontrivial (Fin n) := Finite.one_lt_card_iff_nontrivial.mp
    (by simpa only [Nat.card_fin] using (show 1 < n by omega))
  rcases AlmostSimpleIndexTwoSubnormalClasses.alternating_subnormal_trichotomy
    n hn (topProjection f).range hR with hs | ha | ht
  · have horder : Nat.card A ≤ 2^(n+1) := by
      have h := Nat.card_le_card_of_injective (rangeLift f) (rangeLift_injective f hf)
      rw [PermutationalWreathProduct.natCard_eq,hC,Nat.card_fin] at h
      exact h.trans ((Nat.mul_le_mul_left (2^n) hs).trans_eq (by rw [pow_succ]))
    have hc : Nat.card (ConjClasses A) ≤ Nat.card A :=
      Nat.card_le_card_of_surjective ConjClasses.mk ConjClasses.mk_surjective
    exact (Nat.pow_le_pow_left (hc.trans horder) 3).trans hsmall
  · apply gap_of_counts n p w hC f hf ?_ ?_ hpaired hnum
    · rw [ha]
      have h := AlternatingConjugacyPartitionBound.class_card_le_partitions
        (I := Fin n) (by simpa only [Fintype.card_fin] using (show 2 ≤ n by omega))
      have hp : Nat.card (ConjClasses (alternatingGroup (Fin n))) ≤
          Nat.card (Nat.Partition n) := by simpa only [Fintype.card_fin] using h
      exact hp.trans hpart
    · rw [ha,alternatingGroup.index_eq_two]
  · apply gap_of_counts n p w hC f hf ?_ ?_ hpaired hnum
    · rw [ht]
      have he : Nat.card (ConjClasses (⊤ : Subgroup (Equiv.Perm (Fin n)))) ≤
          Nat.card (ConjClasses (Equiv.Perm (Fin n))) :=
        Nat.card_le_card_of_surjective
          (ConjClasses.map (Subgroup.topEquiv : (⊤ : Subgroup (Equiv.Perm (Fin n))) ≃*
            Equiv.Perm (Fin n)).symm.toMonoidHom)
          (ConjClasses.map_surjective Subgroup.topEquiv.symm.surjective)
      have h := SymmetricConjugacyPartitionBound.class_card_le_partitions (I := Fin n)
      have hp : Nat.card (ConjClasses (Equiv.Perm (Fin n))) ≤
          Nat.card (Nat.Partition n) := by simpa only [Fintype.card_fin] using h
      exact he.trans (hp.trans hpart)
    · rw [ht,Subgroup.index_top]
      decide

theorem class_cube_gap_of_subnormal_top_range
    (n : ℕ) (hC : Nat.card C=2) (hn : 8 ≤ n)
    (f : A →* PermutationalWreathProduct C (Equiv.Perm (Fin n)) (Fin n))
    (hf : Function.Injective f) (hR : (topProjection f).range.IsSubnormal) :
    Nat.card (ConjClasses A)^3 ≤ 5^(2*n-2) := by
  by_cases hten : 10 ≤ n
  · exact BinarySubnormalSymmetricTopClassGap.class_cube_gap_of_subnormal_top_range
      n hC hten f hf hR
  · have he : n=8 ∨ n=9 := by omega
    rcases he with rfl | rfl
    · apply gap_of_partition_counts 8 22 235 (by decide) hC partition_eight_card_le ?_
        (by decide +kernel) (by decide +kernel) f hf hR
      exact (pairedPartitions_card_le_fib_convolution 8).trans_eq (by decide +kernel)
    · apply gap_of_partition_counts 9 43 420 (by decide) hC partition_nine_card_le ?_
        (by decide +kernel) (by decide +kernel) f hf hR
      exact (pairedPartitions_card_le_fib_convolution 9).trans_eq (by decide +kernel)

theorem class_cube_gap_of_subnormal_permutation_top_range
    {I : Type} [Finite I] (hC : Nat.card C=2) (hn : 8 ≤ Nat.card I)
    (f : A →* PermutationalWreathProduct C (Equiv.Perm I) I)
    (hf : Function.Injective f) (hR : (topProjection f).range.IsSubnormal) :
    Nat.card (ConjClasses A)^3 ≤ 5^(2*Nat.card I-2) := by
  let c : I ≃ Fin (Nat.card I) := Finite.equivFinOfCardEq rfl
  let e : Equiv.Perm I ≃* Equiv.Perm (Fin (Nat.card I)) := c.permCongrHom
  have hc : ∀ (q : Equiv.Perm I) (i : I), c (q • i)=e q • c i := by
    intro q i
    change c (q i)=c.permCongr q (c i)
    simp only [Equiv.permCongr_apply,Equiv.symm_apply_apply]
  let w := PermutationalWreathProduct.transport (D := C) e c hc
  let f' := w.toMonoidHom.comp f
  have hf' : Function.Injective f' := w.injective.comp hf
  have hp : topProjection f'=e.toMonoidHom.comp (topProjection f) := by ext a; rfl
  have hR' : (topProjection f').range.IsSubnormal := by
    rw [hp,MonoidHom.range_comp]
    exact Subgroup.IsSubnormal.map e.surjective hR
  exact class_cube_gap_of_subnormal_top_range (Nat.card I) hC hn f' hf' hR'

end SymmetricSubgroupAsymptotics.BinarySubnormalSymmetricTopEightClassGap
