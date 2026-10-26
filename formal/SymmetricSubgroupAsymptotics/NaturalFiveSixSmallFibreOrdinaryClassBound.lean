import SymmetricSubgroupAsymptotics.BinarySubnormalSymmetricTopClassGap
import SymmetricSubgroupAsymptotics.TernarySubnormalSymmetricTopClassGap
import SymmetricSubgroupAsymptotics.AlternatingSmallPartitionCompositionCapacity

/-! Ordinary GM bounds for actual correlated binary/ternary wreath
subgroups with five or six coordinates and a genuinely subnormal natural
symmetric top image. The binary bound uses the SAME actual-range square
inequality; no full-wreath subgroup monotonicity or splitting is used.
Only the existing composition menus of masses5/6 are evaluated. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical BigOperators
namespace SymmetricSubgroupAsymptotics.NaturalFiveSixSmallFibreOrdinaryClassBound
open WreathHomProjectionRange

theorem partition_five_card_le_seven : Nat.card (Nat.Partition 5)≤7 :=
  (FinitePartitionCompositionMenu.partition_card_le_menu_card 5).trans_eq (by decide +kernel)

theorem partition_six_card_le_eleven : Nat.card (Nat.Partition 6)≤11 :=
  (FinitePartitionCompositionMenu.partition_card_le_menu_card 6).trans_eq (by decide +kernel)

theorem subnormal_top_class_card_le (n : ℕ) (hn : n=5 ∨ n=6)
    (R : Subgroup (Equiv.Perm (Fin n))) (hR : R.IsSubnormal) :
    Nat.card (ConjClasses R)≤(if n=5 then 7 else 11) := by
  have hn5 : 5≤n := by omega
  letI : Nontrivial (Fin n) := Finite.one_lt_card_iff_nontrivial.mp
    (by simpa only [Nat.card_fin] using (show 1<n by omega))
  have hp : Nat.card (Nat.Partition n)≤(if n=5 then 7 else 11) := by
    rcases hn with rfl|rfl
    · exact partition_five_card_le_seven
    · exact partition_six_card_le_eleven
  rcases AlmostSimpleIndexTwoSubnormalClasses.alternating_subnormal_trichotomy
      n hn5 R hR with hs|ha|ht
  · exact (Nat.card_le_card_of_surjective ConjClasses.mk ConjClasses.mk_surjective).trans
      (hs.trans (by rcases hn with rfl|rfl <;> decide))
  · rw [ha]
    have h := AlternatingConjugacyPartitionBound.class_card_le_partitions
      (I := Fin n) (by simpa only [Fintype.card_fin] using (show 2≤n by omega))
    have hh : Nat.card (ConjClasses (alternatingGroup (Fin n)))≤Nat.card (Nat.Partition n) := by
      simpa only [Fintype.card_fin] using h
    exact hh.trans hp
  · rw [ht]
    have he : Nat.card (ConjClasses (⊤ : Subgroup (Equiv.Perm (Fin n))))≤
        Nat.card (ConjClasses (Equiv.Perm (Fin n))) :=
      Nat.card_le_card_of_surjective
        (ConjClasses.map (Subgroup.topEquiv : (⊤ : Subgroup (Equiv.Perm (Fin n))) ≃*
          Equiv.Perm (Fin n)).symm.toMonoidHom)
        (ConjClasses.map_surjective Subgroup.topEquiv.symm.surjective)
    have h := SymmetricConjugacyPartitionBound.class_card_le_partitions (I := Fin n)
    have hh : Nat.card (ConjClasses (Equiv.Perm (Fin n)))≤Nat.card (Nat.Partition n) := by
      simpa only [Fintype.card_fin] using h
    exact he.trans (hh.trans hp)

variable {A C : Type} [Group A] [Finite A] [Finite C]

private theorem binary_restricted_class_card_le_index_mul_fib [CommGroup C]
    (n : ℕ) (hC : Nat.card C=2) (R : Subgroup (Equiv.Perm (Fin n))) :
    Nat.card (ConjClasses (PermutationalWreathProduct C R (Fin n)))≤
      R.index*((n+1)*Nat.fib (n+1)) := by
  let N := R.comap (PermutationalWreathProduct.rightHom (D := C) (I := Fin n))
  let e := WreathRestrictedTopClassBound.topPreimageEquiv (C := C) (I := Fin n) R
  have he : Nat.card (ConjClasses (PermutationalWreathProduct C R (Fin n)))≤
      Nat.card (ConjClasses N) :=
    Nat.card_le_card_of_surjective (ConjClasses.map e.symm.toMonoidHom)
      (ConjClasses.map_surjective e.symm.surjective)
  have hfull : Nat.card (ConjClasses
      (PermutationalWreathProduct C (Equiv.Perm (Fin n)) (Fin n)))≤
      (n+1)*Nat.fib (n+1) := by
    have h := (BinaryFullWreathClassBound.class_card_le_pairedPartitions (I := Fin n) hC).trans
      (BinaryPairedPartitionFibonacciGap.pairedPartitions_card_le_fib (Nat.card (Fin n)))
    simpa only [Nat.card_fin] using h
  have hi : N.index=R.index := WreathRestrictedTopClassBound.topPreimage_index R
  exact he.trans ((ConjugacyClassSubgroupIndexBound.class_card_le_index_mul N).trans
    (by
      rw [hi]
      exact Nat.mul_le_mul_left _ hfull))

private theorem binary_gap_of_counts [CommGroup C]
    (n p t : ℕ) (hC : Nat.card C=2)
    (f : A →* PermutationalWreathProduct C (Equiv.Perm (Fin n)) (Fin n))
    (hf : Function.Injective f)
    (hclass : Nat.card (ConjClasses (topProjection f).range)≤p)
    (hwreath : Nat.card (ConjClasses
      (PermutationalWreathProduct C (topProjection f).range (Fin n)))≤t)
    (hnum : (2^n*p*t)^3≤5^(4*n-2)) :
    Nat.card (ConjClasses A)^3≤5^(2*n-1) := by
  have hraw : Nat.card (ConjClasses A)^2≤2^n*
      Nat.card (ConjClasses (topProjection f).range)*
      Nat.card (ConjClasses (PermutationalWreathProduct C (topProjection f).range (Fin n))) := by
    simpa only [hC,Nat.card_fin] using class_square_le_actual_top_range_wreath f hf
  have hsquare : Nat.card (ConjClasses A)^2≤2^n*p*t :=
    hraw.trans (Nat.mul_le_mul (Nat.mul_le_mul_left _ hclass) hwreath)
  have hpow : (Nat.card (ConjClasses A)^3)^2≤(5^(2*n-1))^2 := by
    calc
      _=(Nat.card (ConjClasses A)^2)^3 := by ring
      _≤(2^n*p*t)^3 := Nat.pow_le_pow_left hsquare 3
      _≤5^(4*n-2) := hnum
      _=(5^(2*n-1))^2 := by
        rw [←pow_mul]
        congr 1
        omega
  exact (Nat.pow_le_pow_iff_left (by decide : (2:ℕ)≠0)).mp hpow

theorem binary_class_cube_le_of_subnormal_top_range [CommGroup C]
    (n : ℕ) (hn : n=5 ∨ n=6) (hC : Nat.card C=2)
    (f : A →* PermutationalWreathProduct C (Equiv.Perm (Fin n)) (Fin n))
    (hf : Function.Injective f) (hR : (topProjection f).range.IsSubnormal) :
    Nat.card (ConjClasses A)^3≤5^(2*n-1) := by
  have hn5 : 5≤n := by omega
  letI : Nontrivial (Fin n) := Finite.one_lt_card_iff_nontrivial.mp
    (by simpa only [Nat.card_fin] using (show 1<n by omega))
  rcases AlmostSimpleIndexTwoSubnormalClasses.alternating_subnormal_trichotomy
      n hn5 (topProjection f).range hR with hs|ha|ht
  · have horder : Nat.card A≤2^(n+1) := by
      have h := Nat.card_le_card_of_injective (rangeLift f) (rangeLift_injective f hf)
      rw [PermutationalWreathProduct.natCard_eq,hC,Nat.card_fin] at h
      exact h.trans ((Nat.mul_le_mul_left (2^n) hs).trans_eq (by rw [pow_succ]))
    have hc : Nat.card (ConjClasses A)≤Nat.card A :=
      Nat.card_le_card_of_surjective ConjClasses.mk ConjClasses.mk_surjective
    exact (Nat.pow_le_pow_left (hc.trans horder) 3).trans
      (by rcases hn with rfl|rfl <;> decide +kernel)
  · apply binary_gap_of_counts n (if n=5 then 5 else 11)
      (2*((n+1)*Nat.fib (n+1))) hC f hf
    · rw [ha]
      rcases hn with rfl|rfl
      · exact AlternatingSmallPartitionCompositionCapacity.alternating_five_class_card_le
      · have h := AlternatingConjugacyPartitionBound.class_card_le_partitions
          (I := Fin 6) (by decide)
        have hh : Nat.card (ConjClasses (alternatingGroup (Fin 6)))≤Nat.card (Nat.Partition 6) := by
          simpa only [Fintype.card_fin] using h
        exact hh.trans partition_six_card_le_eleven
    · apply BinarySubnormalSymmetricTopClassGap.restricted_wreath_class_card_le_fib n hC
      rw [ha,alternatingGroup.index_eq_two]
    · rcases hn with rfl|rfl <;> decide +kernel
  · apply binary_gap_of_counts n (if n=5 then 7 else 11)
      ((n+1)*Nat.fib (n+1)) hC f hf
    · exact subnormal_top_class_card_le n hn _ hR
    · have hh := binary_restricted_class_card_le_index_mul_fib n hC (topProjection f).range
      simpa only [ht,Subgroup.index_top,one_mul] using hh
    · rcases hn with rfl|rfl <;> decide +kernel

theorem ternary_class_cube_le_of_subnormal_top_range [Group C]
    (n : ℕ) (hn : n=5 ∨ n=6)
    (horder : Nat.card C≤6) (hC : Nat.card (ConjClasses C)≤3)
    (f : A →* PermutationalWreathProduct C (Equiv.Perm (Fin n)) (Fin n))
    (hf : Function.Injective f) (hR : (topProjection f).range.IsSubnormal) :
    Nat.card (ConjClasses A)^3≤5^(3*n-1) := by
  have hc := WreathSubgroupClassCapacity.class_card_le_capacity_mul_top f hf 3
    (WreathSubgroupClassCapacity.subgroup_class_card_le_three horder hC)
  have hb : Nat.card (ConjClasses A)≤3^n*(if n=5 then 7 else 11) := by
    have hh : Nat.card (ConjClasses A)≤3^n*Nat.card (ConjClasses (topProjection f).range) := by
      simpa only [Nat.card_fin] using hc
    exact hh.trans (Nat.mul_le_mul_left _ (subnormal_top_class_card_le n hn _ hR))
  exact (Nat.pow_le_pow_left hb 3).trans
    (by rcases hn with rfl|rfl <;> decide +kernel)

end SymmetricSubgroupAsymptotics.NaturalFiveSixSmallFibreOrdinaryClassBound
