import SymmetricSubgroupAsymptotics.BinaryEightPointBlocks
import SymmetricSubgroupAsymptotics.PermutationCharacterRankSplit

/-! The eight-block class-count induction on actual binary actions.
The only unproved finite installation is stated explicitly as a base on
all actual binary permutation subgroups of degree at most eight. Original
coordinate kernels and images retain correlations in both induction cases.
This does not install or alter the separate 38/25 nilpotent class input.
-/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics

/-- Class count is transported along an actual group equivalence. -/
theorem conjugacyClass_card_congr {G H : Type*} [Group G] [Group H]
    [Finite G] [Finite H] (e : G ≃* H) :
    Nat.card (ConjClasses G) = Nat.card (ConjClasses H) := by
  apply Nat.le_antisymm
  · exact Nat.card_le_card_of_surjective (ConjClasses.map e.symm.toMonoidHom)
      (ConjClasses.map_surjective e.symm.surjective)
  · exact Nat.card_le_card_of_surjective (ConjClasses.map e.toMonoidHom)
      (ConjClasses.map_surjective e.surjective)

/-- The finite base includes intransitive binary subgroups. Its fourth-power
form has exact integer constants and no supplied all-degree conclusion. -/
def BinaryEightPointClassBase : Prop :=
  ∀ (X : Type) [Finite X] (P : Subgroup (Equiv.Perm X)),
    IsPGroup 2 P → Nat.card X ≤ 8 →
      Nat.card (ConjClasses P) ^ 4 ≤ 5 ^ Nat.card X

namespace BinaryEightBlockClassInduction

theorem base_fourth_bound (hbase : BinaryEightPointClassBase)
    (G X : Type) [Group G] [Finite G] [Finite X]
    [MulAction G X] [FaithfulSMul G X]
    (hG : IsPGroup 2 G) (hsmall : Nat.card X ≤ 8) :
    Nat.card (ConjClasses G) ^ 4 ≤ 5 ^ Nat.card X := by
  let φ : G →* Equiv.Perm X := MulAction.toPermHom G X
  let e : G ≃* φ.range := MonoidHom.ofInjective
    (show Function.Injective φ from MulAction.toPerm_injective)
  rw [conjugacyClass_card_congr e]
  exact hbase X φ.range (hG.of_equiv e) hsmall

theorem base_seventh_bound (hbase : BinaryEightPointClassBase)
    (G X : Type) [Group G] [Finite G] [Finite X]
    [MulAction G X] [FaithfulSMul G X]
    (hG : IsPGroup 2 G) (hsmall : Nat.card X ≤ 8) :
    Nat.card (ConjClasses G) ^ 7 ≤ 5 ^ (2 * Nat.card X) := by
  have hfour := base_fourth_bound hbase G X hG hsmall
  calc
    _ ≤ Nat.card (ConjClasses G) ^ 8 :=
      Nat.pow_le_pow_right (Nat.card_pos (α := ConjClasses G)) (by decide)
    _ = (Nat.card (ConjClasses G) ^ 4) ^ 2 := by rw [← pow_mul]
    _ ≤ (5 ^ Nat.card X) ^ 2 := Nat.pow_le_pow_left hfour 2
    _ = _ := by rw [← pow_mul]; congr 1; omega

/-- A transitive original action of degree greater than eight has a literal
eight-point block system. Only its strictly smaller actual top action uses
the degree-induction hypothesis. -/
theorem transitive_seventh_bound_of_smaller
    (hbase : BinaryEightPointClassBase)
    (G X : Type) [Group G] [Finite G] [Finite X]
    [MulAction G X] [FaithfulSMul G X] [MulAction.IsPretransitive G X]
    (hG : IsPGroup 2 G) (hlarge : 8 < Nat.card X)
    (hsmaller : ∀ (H Y : Type) [Group H] [Finite H] [Finite Y]
      [MulAction H Y] [FaithfulSMul H Y], IsPGroup 2 H → Nat.card Y < Nat.card X →
        Nat.card (ConjClasses H) ^ 7 ≤ 5 ^ (2 * Nat.card Y)) :
    Nat.card (ConjClasses G) ^ 7 ≤ 5 ^ (2 * Nat.card X) := by
  classical
  have hnonempty : Nonempty X := (Nat.card_pos_iff.mp (by omega : 0 < Nat.card X)).1
  let x₀ : X := Classical.choice hnonempty
  obtain ⟨D⟩ := binaryEightPointBlock_nonempty x₀ hG hlarge
  have hlocal : ∀ x (L : Subgroup (Equiv.Perm (D.Fibre x))),
      IsPGroup 2 L → Nat.card (ConjClasses L) ≤ 25 := by
    intro x L hL
    apply (Nat.pow_le_pow_iff_left (by decide : 4 ≠ 0)).mp
    have h := hbase (D.Fibre x) L hL (by rw [D.fibre_card])
    simpa only [D.fibre_card] using h
  have htop := hsmaller D.Top D.Points (D.top_isPGroup hG) D.points_card_lt
  have hblock := OriginalBlockClassBound.class_card_le_power_mul_top
    D.map D.map_equivariant 2 hG 25 hlocal
  change Nat.card (ConjClasses G) ≤
    25 ^ Nat.card D.Points * Nat.card (ConjClasses D.Top) at hblock
  calc
    _ ≤ (25 ^ Nat.card D.Points * Nat.card (ConjClasses D.Top)) ^ 7 :=
      Nat.pow_le_pow_left hblock 7
    _ = (25 ^ Nat.card D.Points) ^ 7 * Nat.card (ConjClasses D.Top) ^ 7 :=
      mul_pow _ _ _
    _ ≤ (25 ^ Nat.card D.Points) ^ 7 * 5 ^ (2 * Nat.card D.Points) :=
      Nat.mul_le_mul_left _ htop
    _ = _ := by
      rw [show (25 : ℕ) = 5 ^ 2 from rfl, ← pow_mul, ← pow_mul, ← pow_add]
      congr 1
      have hdegree := D.degree_product
      omega

open PermutationCharacterRankSplit

/-- An intransitive action splits through its actual restriction image and
the same kernel acting faithfully on the complementary original points. -/
theorem intransitive_seventh_bound_of_smaller
    (G X : Type) [Group G] [Finite G] [Finite X]
    [MulAction G X] [FaithfulSMul G X]
    (hG : IsPGroup 2 G) (ht : ¬MulAction.IsPretransitive G X)
    (hsmaller : ∀ (H Y : Type) [Group H] [Finite H] [Finite Y]
      [MulAction H Y] [FaithfulSMul H Y], IsPGroup 2 H → Nat.card Y < Nat.card X →
        Nat.card (ConjClasses H) ^ 7 ≤ 5 ^ (2 * Nat.card Y)) :
    Nat.card (ConjClasses G) ^ 7 ≤ 5 ^ (2 * Nat.card X) := by
  classical
  obtain ⟨S, hS, hC⟩ := exists_nonempty_proper_invariant ht
  have hdegrees := degrees_lt S hS hC
  letI : FaithfulSMul (Kernel S) ↥(Sᶜ) := kernel_complement_faithful S
  have hI := hsmaller (Image S) S (image_isPGroup S 2 hG) hdegrees.1
  have hK := hsmaller (Kernel S) ↥(Sᶜ) (kernel_isPGroup S 2 hG) hdegrees.2
  have hsplit := conjugacyClass_card_le_normal_mul_quotient (Kernel S)
  have hquot := conjugacyClass_card_congr
    (QuotientGroup.quotientKerEquivOfSurjective (projection S) (projection_surjective S))
  rw [hquot] at hsplit
  calc
    _ ≤ (Nat.card (ConjClasses (Kernel S)) * Nat.card (ConjClasses (Image S))) ^ 7 :=
      Nat.pow_le_pow_left hsplit 7
    _ = Nat.card (ConjClasses (Kernel S)) ^ 7 * Nat.card (ConjClasses (Image S)) ^ 7 :=
      mul_pow _ _ _
    _ ≤ 5 ^ (2 * Nat.card ↥(Sᶜ)) * 5 ^ (2 * Nat.card S) := Nat.mul_le_mul hK hI
    _ = _ := by
      rw [← pow_add]
      congr 1
      have hdegree := card_split S
      omega

end BinaryEightBlockClassInduction

/-- From the explicit finite base only, the complete actual-action induction
gives the integer form of the class bound with rate `5^(2/7)`. -/
theorem permutationTwoGroup_conjugacyClass_pow_seven_le
    (hbase : BinaryEightPointClassBase)
    (G X : Type) [Group G] [Finite G] [Finite X]
    [MulAction G X] [FaithfulSMul G X] (hG : IsPGroup 2 G) :
    Nat.card (ConjClasses G) ^ 7 ≤ 5 ^ (2 * Nat.card X) := by
  classical
  have hmain : ∀ n : ℕ, ∀ (G₀ X₀ : Type) [Group G₀] [Finite G₀] [Finite X₀]
      [MulAction G₀ X₀] [FaithfulSMul G₀ X₀], Nat.card X₀ = n → IsPGroup 2 G₀ →
        Nat.card (ConjClasses G₀) ^ 7 ≤ 5 ^ (2 * Nat.card X₀) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro G₀ X₀ _ _ _ _ _ hdegree hG₀
      have hsmaller : ∀ (H Y : Type) [Group H] [Finite H] [Finite Y]
          [MulAction H Y] [FaithfulSMul H Y], IsPGroup 2 H → Nat.card Y < Nat.card X₀ →
            Nat.card (ConjClasses H) ^ 7 ≤ 5 ^ (2 * Nat.card Y) := by
        intro H Y _ _ _ _ _ hH hlt
        exact ih (Nat.card Y) (by omega) H Y rfl hH
      by_cases hsmall : Nat.card X₀ ≤ 8
      · exact BinaryEightBlockClassInduction.base_seventh_bound hbase G₀ X₀ hG₀ hsmall
      · have hlarge : 8 < Nat.card X₀ := by omega
        by_cases ht : MulAction.IsPretransitive G₀ X₀
        · letI : MulAction.IsPretransitive G₀ X₀ := ht
          exact BinaryEightBlockClassInduction.transitive_seventh_bound_of_smaller
            hbase G₀ X₀ hG₀ hlarge hsmaller
        · exact BinaryEightBlockClassInduction.intransitive_seventh_bound_of_smaller
            G₀ X₀ hG₀ ht hsmaller
  exact hmain (Nat.card X) G X rfl hG

theorem permutationTwoGroup_literal_conjugacyClass_pow_seven_le
    (hbase : BinaryEightPointClassBase)
    (X : Type) [Finite X] (P : Subgroup (Equiv.Perm X)) (hP : IsPGroup 2 P) :
    Nat.card (ConjClasses P) ^ 7 ≤ 5 ^ (2 * Nat.card X) :=
  permutationTwoGroup_conjugacyClass_pow_seven_le hbase P X hP

end SymmetricSubgroupAsymptotics

end
