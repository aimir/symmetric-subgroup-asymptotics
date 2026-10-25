import SymmetricSubgroupAsymptotics.WreathHomProjectionRange
import SymmetricSubgroupAsymptotics.WreathRestrictedTopClassBound
import SymmetricSubgroupAsymptotics.BinaryFullWreathClassBound
import SymmetricSubgroupAsymptotics.BinaryPairedPartitionFibonacciGap
import SymmetricSubgroupAsymptotics.AlmostSimpleIndexTwoSubnormalClasses
import SymmetricSubgroupAsymptotics.AlternatingConjugacyPartitionBound
import SymmetricSubgroupAsymptotics.SymmetricConjugacyPartitionBound

/-! A genuine exponent reserve for correlated binary wreath subgroups
whose ACTUAL top range is subnormal in the full symmetric group. The
source need not be transitive. Small top ranges use order; alternating
and symmetric ranges use paired partitions and the SAME range/index
geometric mean. No full-base comparison or splitting is assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.BinarySubnormalSymmetricTopClassGap
open WreathHomProjectionRange BinaryPairedPartitionFibonacciGap

variable {A C : Type} [Group A] [CommGroup C] [Finite A] [Finite C]

private theorem small_top_order_cube_gap (n : ℕ) (hn : 5 ≤ n) :
    (2^(n+1))^3 ≤ 5^(2*n-2) := by
  induction n,hn using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
    calc
      (2^(n+1+1))^3 = 8*(2^(n+1))^3 := by rw [pow_succ]; ring
      _ ≤ 8*5^(2*n-2) := Nat.mul_le_mul_left _ ih
      _ ≤ 25*5^(2*n-2) := Nat.mul_le_mul_right _ (by decide : (8:ℕ) ≤ 25)
      _ = 5^(2*(n+1)-2) := by
        rw [show 2*(n+1)-2=(2*n-2)+2 by omega,pow_add]
        ring

theorem restricted_wreath_class_card_le_fib
    (n : ℕ) (hC : Nat.card C=2) (R : Subgroup (Equiv.Perm (Fin n)))
    (hindex : R.index ≤ 2) :
    Nat.card (ConjClasses (PermutationalWreathProduct C R (Fin n))) ≤
      2*((n+1)*Nat.fib (n+1)) := by
  let N := R.comap (PermutationalWreathProduct.rightHom (D := C) (I := Fin n))
  let e := WreathRestrictedTopClassBound.topPreimageEquiv (C := C) (I := Fin n) R
  have he : Nat.card (ConjClasses (PermutationalWreathProduct C R (Fin n))) ≤
      Nat.card (ConjClasses N) :=
    Nat.card_le_card_of_surjective (ConjClasses.map e.symm.toMonoidHom)
      (ConjClasses.map_surjective e.symm.surjective)
  have hi : N.index ≤ 2 :=
    (WreathRestrictedTopClassBound.topPreimage_index (C := C) (I := Fin n) R).le.trans hindex
  have hfull : Nat.card (ConjClasses (PermutationalWreathProduct C (Equiv.Perm (Fin n)) (Fin n))) ≤
      (n+1)*Nat.fib (n+1) := by
    have h := (BinaryFullWreathClassBound.class_card_le_pairedPartitions (I := Fin n) hC).trans
      (pairedPartitions_card_le_fib (Nat.card (Fin n)))
    simpa only [Nat.card_fin] using h
  exact he.trans ((ConjugacyClassSubgroupIndexBound.class_card_le_index_mul N).trans
    (Nat.mul_le_mul hi hfull))

private theorem gap_of_top_class_and_index
    (n : ℕ) (hC : Nat.card C=2) (hn : 10 ≤ n)
    (f : A →* PermutationalWreathProduct C (Equiv.Perm (Fin n)) (Fin n))
    (hf : Function.Injective f)
    (hclass : Nat.card (ConjClasses (topProjection f).range) ≤ Nat.fib (n+1))
    (hindex : (topProjection f).range.index ≤ 2) :
    Nat.card (ConjClasses A)^3 ≤ 5^(2*n-2) := by
  have hsquare : Nat.card (ConjClasses A)^2 ≤ 2*budget n := by
    calc
      Nat.card (ConjClasses A)^2 ≤ 2^n *
          Nat.card (ConjClasses (topProjection f).range) *
          Nat.card (ConjClasses (PermutationalWreathProduct C (topProjection f).range (Fin n))) := by
        simpa only [hC,Nat.card_fin] using class_square_le_actual_top_range_wreath f hf
      _ ≤ 2^n*Nat.fib (n+1)*(2*((n+1)*Nat.fib (n+1))) :=
        Nat.mul_le_mul (Nat.mul_le_mul_left _ hclass)
          (restricted_wreath_class_card_le_fib n hC _ hindex)
      _ = 2*budget n := by unfold budget; ring
  have hpow : (Nat.card (ConjClasses A)^3)^2 ≤ (5^(2*n-2))^2 := by
    calc
      (Nat.card (ConjClasses A)^3)^2 = (Nat.card (ConjClasses A)^2)^3 := by ring
      _ ≤ (2*budget n)^3 := Nat.pow_le_pow_left hsquare 3
      _ ≤ 5^(4*n-4) := twice_budget_cube_gap n hn
      _ = (5^(2*n-2))^2 := by rw [← pow_mul]; congr 1; omega
  exact (Nat.pow_le_pow_iff_left (by decide : (2:ℕ) ≠ 0)).mp hpow

theorem class_cube_gap_of_subnormal_top_range
    (n : ℕ) (hC : Nat.card C=2) (hn : 10 ≤ n)
    (f : A →* PermutationalWreathProduct C (Equiv.Perm (Fin n)) (Fin n))
    (hf : Function.Injective f) (hR : (topProjection f).range.IsSubnormal) :
    Nat.card (ConjClasses A)^3 ≤ 5^(2*n-2) := by
  letI : Nontrivial (Fin n) := Finite.one_lt_card_iff_nontrivial.mp
    (by simpa only [Nat.card_fin] using (show 1 < n by omega))
  rcases AlmostSimpleIndexTwoSubnormalClasses.alternating_subnormal_trichotomy
    n (by omega) (topProjection f).range hR with hs | ha | ht
  · have horder : Nat.card A ≤ 2^(n+1) := by
      have h := Nat.card_le_card_of_injective (rangeLift f) (rangeLift_injective f hf)
      rw [PermutationalWreathProduct.natCard_eq,hC,Nat.card_fin] at h
      exact h.trans ((Nat.mul_le_mul_left (2^n) hs).trans_eq (by rw [pow_succ]))
    have hc : Nat.card (ConjClasses A) ≤ Nat.card A :=
      Nat.card_le_card_of_surjective ConjClasses.mk ConjClasses.mk_surjective
    exact (Nat.pow_le_pow_left (hc.trans horder) 3).trans
      (small_top_order_cube_gap n (by omega))
  · apply gap_of_top_class_and_index n hC hn f hf
    · rw [ha]
      have h := AlternatingConjugacyPartitionBound.class_card_le_partitions
        (I := Fin n) (by simpa only [Fintype.card_fin] using (show 2 ≤ n by omega))
      have hpart : Nat.card (ConjClasses (alternatingGroup (Fin n))) ≤
          Nat.card (Nat.Partition n) := by simpa only [Fintype.card_fin] using h
      exact hpart.trans (PartitionFibonacciBound.partition_card_le_fib n)
    · rw [ha,alternatingGroup.index_eq_two]
  · apply gap_of_top_class_and_index n hC hn f hf
    · rw [ht]
      have he : Nat.card (ConjClasses (⊤ : Subgroup (Equiv.Perm (Fin n)))) ≤
          Nat.card (ConjClasses (Equiv.Perm (Fin n))) :=
        Nat.card_le_card_of_surjective
          (ConjClasses.map (Subgroup.topEquiv : (⊤ : Subgroup (Equiv.Perm (Fin n))) ≃*
            Equiv.Perm (Fin n)).symm.toMonoidHom)
          (ConjClasses.map_surjective Subgroup.topEquiv.symm.surjective)
      have h := SymmetricConjugacyPartitionBound.class_card_le_partitions (I := Fin n)
      have hpart : Nat.card (ConjClasses (Equiv.Perm (Fin n))) ≤
          Nat.card (Nat.Partition n) := by simpa only [Fintype.card_fin] using h
      exact he.trans (hpart.trans (PartitionFibonacciBound.partition_card_le_fib n))
    · rw [ht,Subgroup.index_top]
      decide

end SymmetricSubgroupAsymptotics.BinarySubnormalSymmetricTopClassGap
