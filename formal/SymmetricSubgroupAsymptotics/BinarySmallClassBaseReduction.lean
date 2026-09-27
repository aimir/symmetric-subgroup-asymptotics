import SymmetricSubgroupAsymptotics.BinaryEightBlockClassInduction
import Mathlib.Data.Fintype.EquivFin

/-! Reduction of the all-subgroup degree-at-most-eight class base to three
finite transitive bounds. Empty and singleton actions are proved directly;
every intransitive action splits through its original restriction image and
complementary kernel. The finite transitive inputs are still explicit.
-/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics

/-- A class-count bound for every actual transitive binary subgroup on
the specified original finite point set. -/
def TransitiveBinaryClassBound (n c : ℕ) : Prop :=
  ∀ P : Subgroup (Equiv.Perm (Fin n)), IsPGroup 2 P →
    MulAction.IsPretransitive P (Fin n) → Nat.card (ConjClasses P) ≤ c

namespace BinarySmallClassBaseReduction

/-- A point chart transports the entire original action to its actual image
on `Fin n`; it does not replace the group by a catalogue order or class label. -/
theorem class_card_le_of_fin_transitive_bound {n c : ℕ}
    (hbound : TransitiveBinaryClassBound n c)
    (G X : Type) [Group G] [Finite G] [Finite X]
    [MulAction G X] [FaithfulSMul G X] [MulAction.IsPretransitive G X]
    (hG : IsPGroup 2 G) (hdegree : Nat.card X = n) :
    Nat.card (ConjClasses G) ≤ c := by
  classical
  letI : Fintype X := Fintype.ofFinite _
  let e : X ≃ Fin n := Fintype.equivFinOfCardEq
    (by simpa only [← Nat.card_eq_fintype_card] using hdegree)
  let φ : G →* Equiv.Perm (Fin n) :=
    e.permCongrHom.toMonoidHom.comp (MulAction.toPermHom G X)
  have hφ : Function.Injective φ := by
    intro g h hgh
    apply (show Function.Injective (MulAction.toPermHom G X) from MulAction.toPerm_injective)
    exact e.permCongrHom.injective hgh
  let U : Subgroup (Equiv.Perm (Fin n)) := φ.range
  let originalEquiv : G ≃* U := MonoidHom.ofInjective hφ
  letI : MulAction.IsPretransitive U (Fin n) := by
    constructor
    intro x y
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G (e.symm x) (e.symm y)
    refine ⟨φ.rangeRestrict g, ?_⟩
    change e (g • e.symm x) = y
    rw [hg, e.apply_symm_apply]
  rw [conjugacyClass_card_congr originalEquiv]
  exact hbound U (hG.of_equiv originalEquiv) inferInstance

/-- Faithfulness on at most one original point makes the actual group
subsingleton, including the empty action. -/
theorem fourth_bound_of_degree_le_one
    (G X : Type) [Group G] [Finite G] [Finite X]
    [MulAction G X] [FaithfulSMul G X] (hsmall : Nat.card X ≤ 1) :
    Nat.card (ConjClasses G) ^ 4 ≤ 5 ^ Nat.card X := by
  letI : Subsingleton X := Finite.card_le_one_iff_subsingleton.mp hsmall
  letI : Subsingleton G := ⟨fun g h =>
    eq_of_smul_eq_smul (α := X) (fun x => Subsingleton.elim (g • x) (h • x))⟩
  have hclasses : Nat.card (ConjClasses G) ≤ 1 := by
    simpa only [Nat.card_unique] using Nat.card_le_card_of_surjective
      (@ConjClasses.mk G _) ConjClasses.mk_surjective
  have hfour : Nat.card (ConjClasses G) ^ 4 ≤ 1 := by
    simpa only [one_pow] using Nat.pow_le_pow_left hclasses 4
  have hpos : 0 < 5 ^ Nat.card X := Nat.pow_pos (by decide)
  omega

/-- A transitive binary degree is a power of two, so only the three
nontrivial degrees 2, 4 and 8 remain below the finite cutoff. -/
theorem transitive_fourth_bound
    (h2 : TransitiveBinaryClassBound 2 2)
    (h4 : TransitiveBinaryClassBound 4 5)
    (h8 : TransitiveBinaryClassBound 8 25)
    (G X : Type) [Group G] [Finite G] [Finite X]
    [MulAction G X] [FaithfulSMul G X] [MulAction.IsPretransitive G X]
    (hG : IsPGroup 2 G) (hsmall : Nat.card X ≤ 8) :
    Nat.card (ConjClasses G) ^ 4 ≤ 5 ^ Nat.card X := by
  classical
  by_cases hone : Nat.card X ≤ 1
  · exact fourth_bound_of_degree_le_one G X hone
  have hnonempty : Nonempty X :=
    (Nat.card_pos_iff.mp (by omega : 0 < Nat.card X)).1
  let x₀ : X := Classical.choice hnonempty
  obtain ⟨t, ht⟩ := hG.index (MulAction.stabilizer G x₀)
  rw [MulAction.index_stabilizer_of_transitive G x₀] at ht
  have ht3 : t ≤ 3 := by
    apply (Nat.pow_le_pow_iff_right (by decide : 2 ≤ 2)).mp
    simpa only [← ht] using hsmall
  have htcase : t = 0 ∨ t = 1 ∨ t = 2 ∨ t = 3 := by omega
  rcases htcase with rfl | rfl | rfl | rfl
  · have hdeg : Nat.card X = 1 := by simpa using ht
    omega
  · have hdeg : Nat.card X = 2 := by simpa using ht
    have h := class_card_le_of_fin_transitive_bound h2 G X hG hdeg
    rw [hdeg]
    exact (Nat.pow_le_pow_left h 4).trans (by decide)
  · have hdeg : Nat.card X = 4 := by simpa using ht
    have h := class_card_le_of_fin_transitive_bound h4 G X hG hdeg
    rw [hdeg]
    exact Nat.pow_le_pow_left h 4
  · have hdeg : Nat.card X = 8 := by simpa using ht
    have h := class_card_le_of_fin_transitive_bound h8 G X hG hdeg
    rw [hdeg]
    exact (Nat.pow_le_pow_left h 4).trans (by decide)

open PermutationCharacterRankSplit

/-- The original restriction kernel gives the fourth-power intransitive
step, with both recursive degrees strictly smaller. -/
theorem intransitive_fourth_bound_of_smaller
    (G X : Type) [Group G] [Finite G] [Finite X]
    [MulAction G X] [FaithfulSMul G X]
    (hG : IsPGroup 2 G) (ht : ¬MulAction.IsPretransitive G X)
    (hsmaller : ∀ (H Y : Type) [Group H] [Finite H] [Finite Y]
      [MulAction H Y] [FaithfulSMul H Y], IsPGroup 2 H → Nat.card Y < Nat.card X →
        Nat.card (ConjClasses H) ^ 4 ≤ 5 ^ Nat.card Y) :
    Nat.card (ConjClasses G) ^ 4 ≤ 5 ^ Nat.card X := by
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
    _ ≤ (Nat.card (ConjClasses (Kernel S)) * Nat.card (ConjClasses (Image S))) ^ 4 :=
      Nat.pow_le_pow_left hsplit 4
    _ = Nat.card (ConjClasses (Kernel S)) ^ 4 * Nat.card (ConjClasses (Image S)) ^ 4 :=
      mul_pow _ _ _
    _ ≤ 5 ^ Nat.card ↥(Sᶜ) * 5 ^ Nat.card S := Nat.mul_le_mul hK hI
    _ = _ := by
      rw [← pow_add]
      congr 1
      have hdegree := card_split S
      omega

end BinarySmallClassBaseReduction

/-- Only the transitive degrees 2, 4 and 8 require finite installation.
The all-subgroup base, including empty, singleton and intransitive actions,
then follows from the original-action extension argument. -/
theorem binaryEightPointClassBase_of_transitive_bounds
    (h2 : TransitiveBinaryClassBound 2 2)
    (h4 : TransitiveBinaryClassBound 4 5)
    (h8 : TransitiveBinaryClassBound 8 25) : BinaryEightPointClassBase := by
  classical
  have hmain : ∀ n : ℕ, ∀ (G X : Type) [Group G] [Finite G] [Finite X]
      [MulAction G X] [FaithfulSMul G X], Nat.card X = n → Nat.card X ≤ 8 →
      IsPGroup 2 G → Nat.card (ConjClasses G) ^ 4 ≤ 5 ^ Nat.card X := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro G X _ _ _ _ _ hdegree hsmall hG
      have hsmaller : ∀ (H Y : Type) [Group H] [Finite H] [Finite Y]
          [MulAction H Y] [FaithfulSMul H Y], IsPGroup 2 H → Nat.card Y < Nat.card X →
            Nat.card (ConjClasses H) ^ 4 ≤ 5 ^ Nat.card Y := by
        intro H Y _ _ _ _ _ hH hlt
        exact ih (Nat.card Y) (by omega) H Y rfl (by omega) hH
      by_cases ht : MulAction.IsPretransitive G X
      · letI : MulAction.IsPretransitive G X := ht
        exact BinarySmallClassBaseReduction.transitive_fourth_bound
          h2 h4 h8 G X hG hsmall
      · exact BinarySmallClassBaseReduction.intransitive_fourth_bound_of_smaller
          G X hG ht hsmaller
  intro X _ P hP hsmall
  exact hmain (Nat.card X) P X rfl hsmall hP

/-- The complete all-degree bound with exactly the three finite transitive
inputs displayed, rather than an implicit all-subgroup finite-base assumption. -/
theorem permutationTwoGroup_conjugacyClass_pow_seven_le_of_transitive_bounds
    (h2 : TransitiveBinaryClassBound 2 2)
    (h4 : TransitiveBinaryClassBound 4 5)
    (h8 : TransitiveBinaryClassBound 8 25)
    (G X : Type) [Group G] [Finite G] [Finite X]
    [MulAction G X] [FaithfulSMul G X] (hG : IsPGroup 2 G) :
    Nat.card (ConjClasses G) ^ 7 ≤ 5 ^ (2 * Nat.card X) :=
  permutationTwoGroup_conjugacyClass_pow_seven_le
    (binaryEightPointClassBase_of_transitive_bounds h2 h4 h8) G X hG

end SymmetricSubgroupAsymptotics

end
