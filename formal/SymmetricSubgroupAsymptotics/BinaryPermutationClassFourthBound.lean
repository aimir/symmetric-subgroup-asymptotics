import SymmetricSubgroupAsymptotics.BinaryHalfPointBlocks
import SymmetricSubgroupAsymptotics.BinaryPermutationClassBound
import SymmetricSubgroupAsymptotics.BinaryPermutationOrder

/-! The sharp fourth-power class bound for actual binary permutation
actions. Commuting pairs across two original halves supply the transitive
step; the original restriction image and kernel supply the other step. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryPermutationClassFourthBound
open PermutationCharacterRankSplit BinaryHalfPointBlocks

private theorem three_four_pow_le (t : ℕ) (ht : 2 ≤ t) :
    3 * 4 ^ t ≤ 2 * 5 ^ t := by
  induction t, ht using Nat.le_induction with
  | base => decide
  | succ t ht ih =>
    calc
      3 * 4 ^ (t + 1) = 4 * (3 * 4 ^ t) := by rw [pow_succ]; ring
      _ ≤ 4 * (2 * 5 ^ t) := Nat.mul_le_mul_left _ ih
      _ ≤ 5 * (2 * 5 ^ t) := Nat.mul_le_mul_right _ (by decide : 4 ≤ 5)
      _ = 2 * 5 ^ (t + 1) := by rw [pow_succ]; ring

private theorem transitive_step
    (G X : Type) [Group G] [Finite G] [Finite X]
    [MulAction G X] [FaithfulSMul G X] [MulAction.IsPretransitive G X]
    (hG : IsPGroup 2 G) (hlarge : 8 < Nat.card X)
    (ih : ∀ (H Y : Type) [Group H] [Finite H] [Finite Y]
      [MulAction H Y] [FaithfulSMul H Y], IsPGroup 2 H → Nat.card Y < Nat.card X →
        Nat.card (ConjClasses H) ^ 4 ≤ 5 ^ Nat.card Y) :
    Nat.card (ConjClasses G) ^ 4 ≤ 5 ^ Nat.card X := by
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  letI : Nonempty X := (Nat.card_pos_iff.mp (by omega : 0 < Nat.card X)).1
  let x₀ : X := Classical.choice inferInstance
  obtain ⟨s⟩ := pGroup_primeIndexSubgroupChain_exists hG
    (MulAction.stabilizer G x₀) ⊤ le_top
  have hdegree : Nat.card X = 2 ^ s.length := by
    simpa only [Subgroup.relIndex_top_right,
      MulAction.index_stabilizer_of_transitive G x₀] using s.relIndex
  have hk : 3 < s.length := by
    by_contra h
    have hp := Nat.pow_le_pow_right (by decide : 0 < 2)
      (by omega : s.length ≤ 3)
    rw [← hdegree] at hp
    norm_num at hp
    omega
  let r := s.length - 1
  let t := 2 ^ (r - 1)
  have hr : 3 ≤ r := by dsimp [r]; omega
  have hpow : 2 ^ r = 2 * t := by
    dsimp [t]
    conv_lhs => rw [show r = (r - 1) + 1 by omega]
    rw [pow_succ]
    omega
  have hdegree' : Nat.card X = 2 ^ (r + 1) := by
    simpa only [show r + 1 = s.length by dsimp [r]; omega] using hdegree
  obtain ⟨D⟩ := primePowerPointBlock_nonempty x₀ 2 r hG (by
    rw [hdegree']
    exact Nat.pow_lt_pow_right (by decide : 1 < 2) (by omega))
  let S := half D
  have hS : Nat.card S = 2 ^ r := half_card D
  have hC : Nat.card ↥(Sᶜ) = 2 ^ r := complement_card D hdegree'
  let K := D.subgroup
  let N := Kernel (Sᶜ)
  let H := Image (Sᶜ)
  letI : FaithfulSMul N S := {
    eq_of_smul_eq_smul := fun {a b} hab => by
      apply Subtype.ext
      apply eq_of_smul_eq_smul (α := X)
      intro x
      by_cases hx : x ∈ S
      · exact congrArg Subtype.val (hab ⟨x,hx⟩)
      · exact (kernel_fixes (Sᶜ) a ⟨x,hx⟩).trans
          (kernel_fixes (Sᶜ) b ⟨x,hx⟩).symm }
  have hsmaller : 2 ^ r < Nat.card X := by
    rw [hdegree']
    exact Nat.pow_lt_pow_right (by decide : 1 < 2) (by omega)
  have hN : Nat.card (ConjClasses N) ^ 4 ≤ 5 ^ (2 ^ r) := by
    simpa only [hS] using ih N S (kernel_isPGroup (Sᶜ) 2 (hG.to_subgroup K))
      (by rw [hS]; exact hsmaller)
  have hH : Nat.card (ConjClasses H) ^ 4 ≤ 5 ^ (2 ^ r) := by
    simpa only [hC] using ih H ↥(Sᶜ) (image_isPGroup (Sᶜ) 2 (hG.to_subgroup K))
      (by rw [hC]; exact hsmaller)
  have hprod : Nat.card (ConjClasses N) * Nat.card (ConjClasses H) ≤ 5 ^ t := by
    apply (Nat.pow_le_pow_iff_left (by decide : 4 ≠ 0)).mp
    calc
      _ = Nat.card (ConjClasses N)^4 * Nat.card (ConjClasses H)^4 := mul_pow _ _ _
      _ ≤ 5^(2^r) * 5^(2^r) := Nat.mul_le_mul hN hH
      _ = _ := by rw [← pow_add, ← pow_mul]; congr 1; omega
  have hord : Nat.card H ≤ 2 ^ (2 ^ r - 1) :=
    binary_permutation_card_le r hC H (image_isPGroup (Sᶜ) 2 (hG.to_subgroup K))
  have hord2 : 2 * Nat.card H ≤ 4 ^ t := by
    calc
      _ ≤ 2 * 2 ^ (2 ^ r - 1) := Nat.mul_le_mul_left 2 hord
      _ = 2 ^ (2 ^ r) := by
        rw [← pow_succ', Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr (pow_ne_zero r (by decide : (2 : ℕ) ≠ 0)))]
      _ = 4 ^ t := by rw [hpow, show (4 : ℕ) = 2 ^ 2 by decide, ← pow_mul]
  have ht : 2 ≤ t := by
    dsimp [t]
    exact (Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : 1 ≤ r-1))
  have hcost : 3 * Nat.card H ≤ 5 ^ t := by
    have h := three_four_pow_le t ht
    omega
  have hcount := TwoBlockCentralizerProjection.double_class_card_le
    K S (swaps D) (subgroup_index D hdegree')
  have hclass : Nat.card (ConjClasses G) ≤ 5 ^ t := by
    change 2 * Nat.card (ConjClasses G) ≤
      Nat.card (ConjClasses N) * Nat.card (ConjClasses H) + 3 * Nat.card H at hcount
    omega
  calc
    _ ≤ (5 ^ t) ^ 4 := Nat.pow_le_pow_left hclass 4
    _ = _ := by rw [← pow_mul, hdegree', pow_succ]; congr 1; omega

/-- Every finite faithful binary permutation action satisfies the actual
fourth-power class bound. There is no external class-number input. -/
theorem class_card_pow_four_le
    (G X : Type) [Group G] [Finite G] [Finite X]
    [MulAction G X] [FaithfulSMul G X] (hG : IsPGroup 2 G) :
    Nat.card (ConjClasses G) ^ 4 ≤ 5 ^ Nat.card X := by
  classical
  suffices hh : ∀ n (G X : Type) [Group G] [Finite G] [Finite X]
      [MulAction G X] [FaithfulSMul G X], IsPGroup 2 G → Nat.card X = n →
      Nat.card (ConjClasses G)^4 ≤ 5^Nat.card X from hh _ G X hG rfl
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro G X _ _ _ _ _ hG hn
    have hsmaller : ∀ (H Y : Type) [Group H] [Finite H] [Finite Y]
        [MulAction H Y] [FaithfulSMul H Y], IsPGroup 2 H → Nat.card Y < Nat.card X →
        Nat.card (ConjClasses H)^4 ≤ 5^Nat.card Y := by
      intro H Y _ _ _ _ _ hH hlt
      exact ih (Nat.card Y) (by omega) H Y hH rfl
    by_cases hsmall : Nat.card X ≤ 8
    · exact BinaryEightBlockClassInduction.base_fourth_bound
        BinaryPermutationClassBound.finite_base G X hG hsmall
    by_cases ht : MulAction.IsPretransitive G X
    · letI := ht
      exact transitive_step G X hG (by omega) hsmaller
    · obtain ⟨S,hS,hC⟩ := exists_nonempty_proper_invariant ht
      letI : FaithfulSMul (Kernel S) ↥(Sᶜ) := kernel_complement_faithful S
      have hlt := degrees_lt S hS hC
      have hI := hsmaller (Image S) S (image_isPGroup S 2 hG) hlt.1
      have hK := hsmaller (Kernel S) ↥(Sᶜ) (kernel_isPGroup S 2 hG) hlt.2
      have hsplit := conjugacyClass_card_le_normal_mul_quotient (Kernel S)
      have hquot := conjugacyClass_card_congr
        (QuotientGroup.quotientKerEquivOfSurjective (projection S) (projection_surjective S))
      rw [hquot] at hsplit
      calc
        _ ≤ (Nat.card (ConjClasses (Kernel S)) * Nat.card (ConjClasses (Image S)))^4 :=
          Nat.pow_le_pow_left hsplit 4
        _ = Nat.card (ConjClasses (Kernel S))^4 * Nat.card (ConjClasses (Image S))^4 :=
          mul_pow _ _ _
        _ ≤ 5 ^ Nat.card ↥(Sᶜ) * 5 ^ Nat.card S := Nat.mul_le_mul hK hI
        _ = _ := by
          rw [← pow_add]
          congr 1
          have h := card_split S
          omega

end SymmetricSubgroupAsymptotics.BinaryPermutationClassFourthBound
