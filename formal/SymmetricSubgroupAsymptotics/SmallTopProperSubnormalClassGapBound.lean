import SymmetricSubgroupAsymptotics.ActualBlockProperClassPowerDichotomy
import SymmetricSubgroupAsymptotics.SmallTopFullWreathCubeNumerics
import SymmetricSubgroupAsymptotics.WreathSmallTransitiveTopClassBound
import SymmetricSubgroupAsymptotics.GaronziMarotiLargeBlockCubeReduction
import SymmetricSubgroupAsymptotics.SmallPermutationClassBudgets
import Mathlib.GroupTheory.IsSubnormal

/-! The ordinary strict-smaller GM induction hypothesis suffices on a
saturated full base. Only PROPER subnormal component groups need an
extra power in the deficient-kernel branch. Thus simple components are
handled with no additional class-capacity assumption. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.SmallTopProperSubnormalClassGapBound
open OriginalBlockClassBound

variable {A Ω X : Type} [Group A] [MulAction A Ω] [MulAction A X]
    [MulAction.IsPretransitive A X] [FaithfulSMul A Ω]
    [Finite A] [Finite Ω] [Finite X]
    (b : Ω → X) (hb : ∀ (g : A) (ω : Ω), b (g • ω) = g • b ω) (x0 : X)

theorem class_cube_le_of_proper_subnormal_gaps (a : ℕ) (ha : 4 ≤ a)
    (hsize : Nat.card (originalBlockFibre b x0) = a)
    (hblocks : Nat.card X = 2 ∨ Nat.card X = 3)
    (hproper : ∀ L : Subgroup (originalBlockComponent b hb x0), L.IsSubnormal → L ≠ ⊤ →
      Nat.card (ConjClasses L) ^ 3 ≤ 5 ^ (a - 2))
    (hSmaller : ∀ m : ℕ, m < Nat.card Ω → 4 ≤ m →
      ∀ L : Subgroup (Equiv.Perm (Fin m)),
        Nat.card (ConjClasses L) ^ 3 ≤ 5 ^ (m - 1)) :
    Nat.card (ConjClasses A) ^ 3 ≤ 5 ^ (Nat.card Ω - 1) := by
  let C := originalBlockComponent b hb x0
  let T := Top (A := A) (X := X)
  have hd : Nat.card Ω = a * Nat.card X := by
    have h := Nat.card_congr (ActualBlockWreathEmbedding.productEquiv b hb x0)
    rw [Nat.card_prod, hsize] at h
    exact h.symm
  have halt : a < Nat.card Ω := by
    rw [hd]
    rcases hblocks with h | h <;> rw [h] <;> omega
  have hbudget (L : Subgroup C) (_hL : L.IsSubnormal) :
      Nat.card (ConjClasses L) ^ 3 ≤ 5 ^ (a - 1) := by
    have hlocal := GaronziMarotiLargeBlockCubeReduction.cube_le_of_finite_permutation_bound
      (originalBlockFibre b x0) (5 ^ (Nat.card (originalBlockFibre b x0) - 1))
      (hSmaller _ (by rwa [hsize]) (by rwa [hsize])) (L.map C.subtype)
    let e := L.equivMapOfInjective C.subtype Subtype.val_injective
    have he : Nat.card (ConjClasses L) ≤ Nat.card (ConjClasses (L.map C.subtype)) :=
      Nat.card_le_card_of_surjective (ConjClasses.map e.symm.toMonoidHom)
        (ConjClasses.map_surjective e.symm.surjective)
    exact (Nat.pow_le_pow_left he 3).trans (by simpa only [hsize] using hlocal)
  have hC : Nat.card (ConjClasses C) ^ 3 ≤ 5 ^ (a - 1) :=
    GaronziMarotiLargeBlockCubeReduction.cube_le_of_finite_permutation_bound
      (originalBlockFibre b x0) (5 ^ (a - 1))
      (by
        intro L
        have hlocal := hSmaller (Nat.card (originalBlockFibre b x0))
          (by rwa [hsize]) (by rwa [hsize]) L
        simpa only [hsize] using hlocal) C
  rcases ActualBlockProperClassPowerDichotomy.class_power_saving_or_full_wreath
      b hb x0 3 (5 ^ (a - 1)) (5 ^ (a - 2)) hbudget hproper with hsaving | hfull
  · have ht : Nat.card (ConjClasses T) ≤ Nat.card X := by
      rcases hblocks with h | h
      · rw [h]
        exact SmallPermutationClassBudgets.subgroup_class_card_le_two h.le _
      · rw [h]
        exact SmallPermutationClassBudgets.subgroup_class_card_le_three h.le _
    exact hsaving.trans (by
      simpa only [hd] using SmallTopFullWreathCubeNumerics.proper_kernel_budget
        a (Nat.card X) (Nat.card (ConjClasses T)) ha hblocks ht)
  · let e := Classical.choice hfull
    have he : Nat.card (ConjClasses A) =
        Nat.card (ConjClasses (PermutationalWreathProduct C T X)) := conjugacyClass_card_congr e
    letI : MulAction.IsPretransitive T X := ⟨fun x y => by
      obtain ⟨g, hg⟩ := MulAction.exists_smul_eq A x y
      exact ⟨(topMap (A := A) (X := X)).rangeRestrict g, hg⟩⟩
    rw [he, hd]
    rcases hblocks with htwo | hthree
    · rw [htwo]
      have hW := WreathSmallTransitiveTopClassBound.pair_class_card_le (C := C) T htwo
      exact (Nat.pow_le_pow_left hW 3).trans (by
        simpa only [Nat.mul_comm] using
          SmallTopFullWreathCubeNumerics.pair_budget a (Nat.card (ConjClasses C)) ha hC)
    · rw [hthree]
      have hW := WreathSmallTransitiveTopClassBound.triple_class_card_le (C := C) T hthree
      exact (Nat.pow_le_pow_left hW 3).trans (by
        simpa only [Nat.mul_comm] using
          SmallTopFullWreathCubeNumerics.triple_budget a (Nat.card (ConjClasses C)) ha hC)

theorem class_cube_le_of_simple_component
    [IsSimpleGroup (originalBlockComponent b hb x0)]
    (a : ℕ) (ha : 4 ≤ a) (hsize : Nat.card (originalBlockFibre b x0) = a)
    (hblocks : Nat.card X = 2 ∨ Nat.card X = 3)
    (hSmaller : ∀ m : ℕ, m < Nat.card Ω → 4 ≤ m →
      ∀ L : Subgroup (Equiv.Perm (Fin m)),
        Nat.card (ConjClasses L) ^ 3 ≤ 5 ^ (m - 1)) :
    Nat.card (ConjClasses A) ^ 3 ≤ 5 ^ (Nat.card Ω - 1) := by
  apply class_cube_le_of_proper_subnormal_gaps b hb x0 a ha hsize hblocks ?_ hSmaller
  intro L hL hne
  rcases Subgroup.IsSubnormal.eq_bot_or_top_of_isSimpleGroup inferInstance hL with hbot | htop
  · subst L
    have hle := Nat.card_le_card_of_surjective
      (@ConjClasses.mk (⊥ : Subgroup (originalBlockComponent b hb x0)) _) ConjClasses.mk_surjective
    have hc : Nat.card (ConjClasses (⊥ : Subgroup (originalBlockComponent b hb x0))) ≤ 1 := by
      simpa only [Nat.card_unique] using hle
    have hp : 0 < (5 : ℕ) ^ (a - 2) := pow_pos (by decide) _
    exact (Nat.pow_le_pow_left hc 3).trans (by simpa only [one_pow] using Nat.succ_le_of_lt hp)
  · exact (hne htop).elim

end SymmetricSubgroupAsymptotics.SmallTopProperSubnormalClassGapBound
