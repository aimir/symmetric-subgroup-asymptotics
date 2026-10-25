import SymmetricSubgroupAsymptotics.SmallTopPrimitiveFourComponentClassBound
import SymmetricSubgroupAsymptotics.WreathSmallTransitiveTopClassBound

/-! The literal two- and three-block class bound for primitive
four-point components. Proper correlated kernels use the strict
coordinate saving; saturated kernels use an actual full-wreath
equivalence and the noncommutative cycle class code. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.SmallTopPrimitiveFourClassBound
open OriginalBlockClassBound

theorem class_cube_le
    {A Ω X : Type} [Group A] [MulAction A Ω] [MulAction A X]
    [MulAction.IsPretransitive A X] [FaithfulSMul A Ω]
    [Finite A] [Finite Ω] [Finite X]
    (b : Ω → X) (hb : ∀ (a : A) (ω : Ω), b (a • ω) = a • b ω) (x0 : X)
    (hblocks : Nat.card X = 2 ∨ Nat.card X = 3)
    (hprimitive : MulAction.IsPreprimitive
      (originalBlockComponent b hb x0) (originalBlockFibre b x0))
    (hdegree : Nat.card (originalBlockFibre b x0) = 4) :
    Nat.card (ConjClasses A) ^ 3 ≤ 5 ^ (Nat.card Ω - 1) := by
  rcases SmallTopPrimitiveFourComponentClassBound.class_cube_or_symmetric_full_wreath
    b hb x0 hblocks hprimitive hdegree with h | hfull
  · exact h
  · let C := originalBlockComponent b hb x0
    let T := Top (A := A) (X := X)
    let e := Classical.choice hfull.2
    have hC : Nat.card (ConjClasses C) ≤ 5 :=
      FourPointPermutationClassBound.faithful_action_class_card_le_five
        C (originalBlockFibre b x0) hdegree
    letI : MulAction.IsPretransitive T X := ⟨fun x y => by
      obtain ⟨g,hg⟩ := MulAction.exists_smul_eq A x y
      exact ⟨(topMap (A := A) (X := X)).rangeRestrict g,hg⟩⟩
    have hd : Nat.card Ω = 4 * Nat.card X := by
      have h := Nat.card_congr (ActualBlockWreathEmbedding.productEquiv b hb x0)
      rw [Nat.card_prod,hdegree] at h
      exact h.symm
    have he : Nat.card (ConjClasses A) =
        Nat.card (ConjClasses (PermutationalWreathProduct C T X)) :=
      conjugacyClass_card_congr e
    rcases hblocks with htwo | hthree
    · have hW := WreathSmallTransitiveTopClassBound.pair_class_card_le
        (C := C) T htwo
      have hp := Nat.pow_le_pow_left hC 2
      have hA : Nat.card (ConjClasses A) ≤ 30 := by rw [he]; omega
      exact (Nat.pow_le_pow_left hA 3).trans (by rw [hd,htwo]; decide +kernel)
    · have hW := WreathSmallTransitiveTopClassBound.triple_class_card_le
        (C := C) T hthree
      have hp := Nat.pow_le_pow_left hC 3
      have hA : Nat.card (ConjClasses A) ≤ 270 := by rw [he]; omega
      exact (Nat.pow_le_pow_left hA 3).trans (by rw [hd,hthree]; decide +kernel)

end SymmetricSubgroupAsymptotics.SmallTopPrimitiveFourClassBound
