import SymmetricSubgroupAsymptotics.CFSGPrimeBoundedWordEncoding
import SymmetricSubgroupAsymptotics.CFSGOrdinaryLargePrimeSubdirectCount
import SymmetricSubgroupAsymptotics.CFSGOrdinaryTernarySubdirectCount
import SymmetricSubgroupAsymptotics.MarkedC4ActualBinarySkeletonMenu

/-! Genuine ordinary bounded odd-prime counting. Actual orbit words and
original labels are encoded before their actual nilpotent subdirect sources
are counted. Every alphabet constant depends only on the cutoff. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option Elab.async false
noncomputable section
open scoped Classical BigOperators
namespace SymmetricSubgroupAsymptotics.CFSGPrimeBoundedSkeletonCount
open MarkedC4 FiniteOrbitWordShapes FiniteBinaryWordTargets
open CFSGPrimeBoundedWordEncoding

/-- The original small permutation alphabet is finite independently of p. -/
theorem skeleton_card_le (p C b : ℕ) :
    Nat.card (Skeleton p C b) ≤
      (b+1)*(max C 1)^b*(ActualBinarySkeletonMenu.letterBound C)^b := by
  have hi := Nat.card_le_card_of_injective
    (fun q : Skeleton p C b => q.val) Subtype.val_injective
  have hc : Nat.card (Σ S : Shape C b,LocalGroups S) ≤
      Nat.card (Shape C b)*(ActualBinarySkeletonMenu.letterBound C)^b := by
    rw [Nat.card_sigma]
    calc
      _ ≤ ∑ _S : Shape C b,(ActualBinarySkeletonMenu.letterBound C)^b :=
        Finset.sum_le_sum (fun S _ => ActualBinarySkeletonMenu.local_card_le S)
      _ = _ := by simp [Nat.card_eq_fintype_card]
  exact (hi.trans hc).trans
    (Nat.mul_le_mul_right _ (ActualBinarySkeletonMenu.shape_card_le C b))

theorem letter_card_le {C : ℕ} (d : Fin C) (U : Subgroup (Equiv.Perm (Fin d.val))) :
    Nat.card U ≤ C.factorial := by
  have h := Nat.card_le_card_of_injective U.subtype Subtype.val_injective
  have hperm : Nat.card (Equiv.Perm (Fin d.val))=d.val.factorial := by
    simp only [Nat.card_perm,Nat.card_fin]
  rw [hperm] at h
  exact h.trans (Nat.factorial_le d.isLt.le)

theorem letter_log_le {C : ℕ} (d : Fin C) (U : Subgroup (Equiv.Perm (Fin d.val))) :
    Real.logb 2 (Nat.card U) ≤ (C.factorial : ℝ) := by
  apply (Real.logb_le_iff_le_rpow (by norm_num : (1 : ℝ) < 2)
    (show (0 : ℝ) < Nat.card U by exact_mod_cast Nat.card_pos)).mpr
  rw [Real.rpow_natCast]
  exact_mod_cast (letter_card_le d U).trans (Nat.lt_two_pow_self (n := C.factorial)).le

/-- Every original bounded physical word has one uniform quadratic count;
only its actual factor alphabets contribute to the lower-order term. -/
theorem word_family_card_le (p C b : ℕ) [Fact p.Prime] (hp : 3 ≤ p)
    (q : Skeleton p C b) :
    (Nat.card (ActualWordMenuPartition.Family (Factors q)) : ℝ) ≤
      (b.factorial*(b+1)^((2^C.factorial)*b) : ℕ)*
        (2 : ℝ)^((b : ℝ)^2/16+(b : ℝ)*(C.factorial : ℝ)^2) := by
  let t := q.val.1.length.val
  let X : Fin t → Type := fun i => Fin (q.val.1.degrees i).val
  let U : ∀ i,Subgroup (Equiv.Perm (X i)) := q.val.2
  letI (i : Fin t) : Nonempty (X i) := ⟨⟨0,q.val.1.positive i⟩⟩
  letI (i : Fin t) : MulAction.IsPretransitive (U i) (X i) := ⟨q.property.2 i⟩
  have hU : ∀ i,IsPGroup p (U i) := q.property.1
  have hcard : ∀ i,Nat.card (U i) ≤ C.factorial := fun i => letter_card_le _ _
  have hlog : ∀ i,Real.logb 2 (Nat.card (U i)) ≤ (C.factorial : ℝ) := fun i => letter_log_le _ _
  have htotal : (∑ i : Fin t,(Nat.card (X i) : ℝ))=(b : ℝ) := by
    have hn := q.val.1.total
    simpa only [X,Nat.card_fin] using (show (∑ i : Fin t,((q.val.1.degrees i).val : ℝ))=b by exact_mod_cast hn)
  have hlocal : (Nat.card (ActualWordMenuPartition.Family (Factors q)) : ℝ) ≤
      (t.factorial*(t+1)^((2^C.factorial)*t) : ℕ)*
        (2 : ℝ)^((b : ℝ)^2/16+(t : ℝ)*(C.factorial : ℝ)^2) := by
    by_cases hp3 : p=3
    · subst p
      have hh := CFSGOrdinaryTernarySubdirectCount.subdirect_card_le X U hU
        (C.factorial : ℝ) C.factorial hlog hcard
      rw [htotal] at hh
      apply hh.trans
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
      have hm := mul_le_mul_of_nonneg_right CFSGOrdinaryTernarySubdirectCount.ternary_coefficient_lt.le
        (sq_nonneg (b : ℝ))
      nlinarith
    · have hp5 : 5 ≤ p := by
        have hprime : p.Prime := Fact.out
        have hp4 : p≠4 := by intro h;rw [h] at hprime;norm_num at hprime
        omega
      have hh := CFSGOrdinaryLargePrimeSubdirectCount.subdirect_card_le p hp5 X U hU
        (C.factorial : ℝ) C.factorial hlog hcard
      simpa only [htotal] using hh
  have htb : t ≤ b := Nat.le_of_lt_succ q.val.1.length.isLt
  have hmenu : t.factorial*(t+1)^((2^C.factorial)*t) ≤
      b.factorial*(b+1)^((2^C.factorial)*b) := by
    apply Nat.mul_le_mul (Nat.factorial_le htb)
    exact (Nat.pow_le_pow_left (by omega : t+1 ≤ b+1) _).trans
      (Nat.pow_le_pow_right (by omega : 0 < b+1) (Nat.mul_le_mul_left _ htb))
  apply hlocal.trans
  apply mul_le_mul (by exact_mod_cast hmenu) _ (by positivity) (Nat.cast_nonneg _)
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
  have htbR : (t : ℝ) ≤ b := by exact_mod_cast htb
  nlinarith [sq_nonneg (C.factorial : ℝ)]

/-- A fixed-cutoff odd-prime family is bounded without an ordinary all-
subgroup theorem or any prime-group counting hypothesis. -/
theorem bounded_odd_prime_card_le (p C b : ℕ) [Fact p.Prime] (hp : 3 ≤ p) :
    (Nat.card {G : Subgroup (PermutationGroup b) // IsPGroup p G ∧
      OrbitCutoffFamilies.OrbitCutoff C G} : ℝ) ≤
      (b.factorial*((b+1)*(max C 1)^b*(ActualBinarySkeletonMenu.letterBound C)^b)*
        (b.factorial*(b+1)^((2^C.factorial)*b)) : ℕ)*
        (2 : ℝ)^((b : ℝ)^2/16+(b : ℝ)*(C.factorial : ℝ)^2) := by
  let S := Skeleton p C b
  letI : Fintype S := Fintype.ofFinite _
  have ht : Nat.card (Target p C b)=∑ q : S,Nat.card (ActualWordMenuPartition.Family (Factors q)) :=
    Nat.card_sigma
  have hT : (Nat.card (Target p C b) : ℝ) ≤
      (Nat.card S : ℝ)*(b.factorial*(b+1)^((2^C.factorial)*b) : ℕ)*
        (2 : ℝ)^((b : ℝ)^2/16+(b : ℝ)*(C.factorial : ℝ)^2) := by
    rw [ht]
    push_cast
    calc
      _ ≤ ∑ _q : S,(b.factorial*(b+1)^((2^C.factorial)*b) : ℕ)*
          (2 : ℝ)^((b : ℝ)^2/16+(b : ℝ)*(C.factorial : ℝ)^2) :=
        Finset.sum_le_sum (fun q _ => word_family_card_le p C b hp q)
      _ = _ := by simp [Nat.card_eq_fintype_card,mul_assoc]
  have hS : (Nat.card S : ℝ) ≤
      ((b+1)*(max C 1)^b*(ActualBinarySkeletonMenu.letterBound C)^b : ℕ) := by
    exact_mod_cast skeleton_card_le p C b
  have hsource := CFSGPrimeBoundedWordEncoding.bounded_prime_card_le p C b
  have hsourceR : (Nat.card {G : Subgroup (PermutationGroup b) // IsPGroup p G ∧
      OrbitCutoffFamilies.OrbitCutoff C G} : ℝ) ≤ (b.factorial : ℝ)*Nat.card (Target p C b) := by
    exact_mod_cast hsource
  apply hsourceR.trans
  calc
    _ ≤ (b.factorial : ℝ)*((Nat.card S : ℝ)*(b.factorial*(b+1)^((2^C.factorial)*b) : ℕ)*
      (2 : ℝ)^((b : ℝ)^2/16+(b : ℝ)*(C.factorial : ℝ)^2)) :=
      mul_le_mul_of_nonneg_left hT (Nat.cast_nonneg _)
    _ ≤ _ := by
      push_cast
      have hm := mul_le_mul_of_nonneg_left hS
        (show 0 ≤ (b.factorial : ℝ)*(b.factorial*(b+1)^((2^C.factorial)*b) : ℕ)*
          (2 : ℝ)^((b : ℝ)^2/16+(b : ℝ)*(C.factorial : ℝ)^2) by positivity)
      convert hm using 1 <;> push_cast <;> ring

end SymmetricSubgroupAsymptotics.CFSGPrimeBoundedSkeletonCount
