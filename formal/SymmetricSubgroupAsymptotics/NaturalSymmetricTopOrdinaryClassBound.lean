import SymmetricSubgroupAsymptotics.NaturalFiveSixSmallFibreOrdinaryClassBound
import SymmetricSubgroupAsymptotics.BinarySubnormalSymmetricTopEightClassGap

/-! Ordinary small-fibre bounds for every natural symmetric coordinate
set of size at least five. The binary proof uses the actual-range square
bound at seven coordinates and the checked stronger tail. The ternary
proof uses actual coordinate-subgroup capacity three directly, retaining
the projected range rather than replacing it by a full wreath group. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.NaturalSymmetricTopOrdinaryClassBound
open WreathHomProjectionRange

theorem partition_seven_card_le_fifteen : Nat.card (Nat.Partition 7)≤15 :=
  (FinitePartitionCompositionMenu.partition_card_le_menu_card 7).trans_eq (by decide +kernel)

theorem three_mul_fib_succ_le (n : ℕ) (hn : 3≤n) :
    3*Nat.fib (n+2)≤5*Nat.fib (n+1) := by
  have h0 := Nat.fib_add_two (n := n-2)
  have h1 := Nat.fib_add_two (n := n-1)
  have hm := Nat.fib_mono (show n-2≤n-1 by omega)
  rw [show n-2+2=n by omega,show n-2+1=n-1 by omega] at h0
  rw [show n-1+2=n+1 by omega,show n-1+1=n by omega] at h1
  rw [Nat.fib_add_two]
  omega

theorem ternary_fib_cube_le (n : ℕ) (hn : 8≤n) :
    (3^n*Nat.fib (n+1))^3≤5^(3*n-1) := by
  induction n,hn using Nat.le_induction with
  | base => decide +kernel
  | succ n hn ih =>
    have hs : 3^(n+1)*Nat.fib ((n+1)+1)≤5*(3^n*Nat.fib (n+1)) := by
      calc
        _=3^n*(3*Nat.fib (n+2)) := by rw [pow_succ]; ring
        _≤3^n*(5*Nat.fib (n+1)) := Nat.mul_le_mul_left _ (three_mul_fib_succ_le n (by omega))
        _=5*(3^n*Nat.fib (n+1)) := by ring
    calc
      _≤(5*(3^n*Nat.fib (n+1)))^3 := Nat.pow_le_pow_left hs 3
      _=125*(3^n*Nat.fib (n+1))^3 := by ring
      _≤125*5^(3*n-1) := Nat.mul_le_mul_left _ ih
      _=5^(3*(n+1)-1) := by
        rw [show 3*(n+1)-1=(3*n-1)+3 by omega,pow_add]
        ring

private theorem subnormal_top_class_card_le_bound
    (n : ℕ) (hn : 5≤n) (p : ℕ) (hp2 : 2≤p)
    (hp : Nat.card (Nat.Partition n)≤p)
    (R : Subgroup (Equiv.Perm (Fin n))) (hR : R.IsSubnormal) :
    Nat.card (ConjClasses R)≤p := by
  letI : Nontrivial (Fin n) := Finite.one_lt_card_iff_nontrivial.mp
    (by simpa only [Nat.card_fin] using (show 1<n by omega))
  rcases AlmostSimpleIndexTwoSubnormalClasses.alternating_subnormal_trichotomy
      n hn R hR with hs|ha|ht
  · exact (Nat.card_le_card_of_surjective ConjClasses.mk ConjClasses.mk_surjective).trans
      (hs.trans hp2)
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

private theorem binary_seven [CommGroup C] (hC : Nat.card C=2)
    (f : A →* PermutationalWreathProduct C (Equiv.Perm (Fin 7)) (Fin 7))
    (hf : Function.Injective f) (hR : (topProjection f).range.IsSubnormal) :
    Nat.card (ConjClasses A)^3≤5^13 := by
  have hclass : Nat.card (ConjClasses (topProjection f).range)≤15 :=
    subnormal_top_class_card_le_bound 7 (by decide) 15 (by decide)
      partition_seven_card_le_fifteen _ hR
  rcases AlmostSimpleIndexTwoSubnormalClasses.alternating_subnormal_trichotomy
      7 (by decide) (topProjection f).range hR with hs|ha|ht
  · have horder : Nat.card A≤2^8 := by
      have h := Nat.card_le_card_of_injective (rangeLift f) (rangeLift_injective f hf)
      rw [PermutationalWreathProduct.natCard_eq,hC,Nat.card_fin] at h
      exact h.trans (Nat.mul_le_mul_left _ hs)
    have hc : Nat.card (ConjClasses A)≤Nat.card A :=
      Nat.card_le_card_of_surjective ConjClasses.mk ConjClasses.mk_surjective
    exact (Nat.pow_le_pow_left (hc.trans horder) 3).trans (by decide +kernel)
  all_goals
    have hi : (topProjection f).range.index≤2 := by
      first | rw [ha,alternatingGroup.index_eq_two] | rw [ht,Subgroup.index_top]; decide
    have hw : Nat.card (ConjClasses
        (PermutationalWreathProduct C (topProjection f).range (Fin 7)))≤336 := by
      have hh := BinarySubnormalSymmetricTopClassGap.restricted_wreath_class_card_le_fib
        7 hC (topProjection f).range hi
      exact hh.trans_eq (by decide +kernel)
    have hsquare : Nat.card (ConjClasses A)^2≤2^7*15*336 := by
      have hh := class_square_le_actual_top_range_wreath f hf
      rw [hC,Nat.card_fin] at hh
      exact hh.trans (Nat.mul_le_mul (Nat.mul_le_mul_left _ hclass) hw)
    have hpow : (Nat.card (ConjClasses A)^3)^2≤(5^13)^2 := by
      calc
        _=(Nat.card (ConjClasses A)^2)^3 := by ring
        _≤(2^7*15*336)^3 := Nat.pow_le_pow_left hsquare 3
        _≤_ := by decide +kernel
    exact (Nat.pow_le_pow_iff_left (by decide : (2:ℕ)≠0)).mp hpow

theorem binary_class_cube_le_of_subnormal_top_range [CommGroup C]
    (n : ℕ) (hn : 5≤n) (hC : Nat.card C=2)
    (f : A →* PermutationalWreathProduct C (Equiv.Perm (Fin n)) (Fin n))
    (hf : Function.Injective f) (hR : (topProjection f).range.IsSubnormal) :
    Nat.card (ConjClasses A)^3≤5^(2*n-1) := by
  by_cases h8 : 8≤n
  · exact (BinarySubnormalSymmetricTopEightClassGap.class_cube_gap_of_subnormal_top_range
      n hC h8 f hf hR).trans (Nat.pow_le_pow_right (by decide) (by omega))
  · have he : n=5 ∨ n=6 ∨ n=7 := by omega
    rcases he with h5|h6|rfl
    · exact NaturalFiveSixSmallFibreOrdinaryClassBound.binary_class_cube_le_of_subnormal_top_range
        n (Or.inl h5) hC f hf hR
    · exact NaturalFiveSixSmallFibreOrdinaryClassBound.binary_class_cube_le_of_subnormal_top_range
        n (Or.inr h6) hC f hf hR
    · exact binary_seven hC f hf hR

theorem ternary_class_cube_le_of_subnormal_top_range [Group C]
    (n : ℕ) (hn : 5≤n) (horder : Nat.card C≤6) (hC : Nat.card (ConjClasses C)≤3)
    (f : A →* PermutationalWreathProduct C (Equiv.Perm (Fin n)) (Fin n))
    (hf : Function.Injective f) (hR : (topProjection f).range.IsSubnormal) :
    Nat.card (ConjClasses A)^3≤5^(3*n-1) := by
  by_cases h8 : 8≤n
  · have hc := WreathSubgroupClassCapacity.class_card_le_capacity_mul_top f hf 3
      (WreathSubgroupClassCapacity.subgroup_class_card_le_three horder hC)
    have htop : Nat.card (ConjClasses (topProjection f).range)≤Nat.fib (n+1) :=
      subnormal_top_class_card_le_bound n hn (Nat.fib (n+1))
        ((by decide : 2≤Nat.fib 6).trans (Nat.fib_mono (by omega)))
        (PartitionFibonacciBound.partition_card_le_fib n) _ hR
    have hh : Nat.card (ConjClasses A)≤3^n*Nat.fib (n+1) := by
      have hc' : Nat.card (ConjClasses A)≤3^n*Nat.card (ConjClasses (topProjection f).range) := by
        simpa only [Nat.card_fin] using hc
      exact hc'.trans (Nat.mul_le_mul_left _ htop)
    exact (Nat.pow_le_pow_left hh 3).trans (ternary_fib_cube_le n h8)
  · have he : n=5 ∨ n=6 ∨ n=7 := by omega
    rcases he with h5|h6|rfl
    · exact NaturalFiveSixSmallFibreOrdinaryClassBound.ternary_class_cube_le_of_subnormal_top_range
        n (Or.inl h5) horder hC f hf hR
    · exact NaturalFiveSixSmallFibreOrdinaryClassBound.ternary_class_cube_le_of_subnormal_top_range
        n (Or.inr h6) horder hC f hf hR
    · have hc := WreathSubgroupClassCapacity.class_card_le_capacity_mul_top f hf 3
        (WreathSubgroupClassCapacity.subgroup_class_card_le_three horder hC)
      have htop : Nat.card (ConjClasses (topProjection f).range)≤15 :=
        subnormal_top_class_card_le_bound 7 (by decide) 15 (by decide)
          partition_seven_card_le_fifteen _ hR
      have hh : Nat.card (ConjClasses A)≤3^7*15 := by
        have hc' : Nat.card (ConjClasses A)≤3^7*Nat.card (ConjClasses (topProjection f).range) := by
          simpa only [Nat.card_fin] using hc
        exact hc'.trans (Nat.mul_le_mul_left _ htop)
      exact (Nat.pow_le_pow_left hh 3).trans (by decide +kernel)

end SymmetricSubgroupAsymptotics.NaturalSymmetricTopOrdinaryClassBound
