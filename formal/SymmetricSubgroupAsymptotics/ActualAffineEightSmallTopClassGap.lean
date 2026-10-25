import SymmetricSubgroupAsymptotics.AffineDegreeEightSubgroupClassGap
import SymmetricSubgroupAsymptotics.SmallTopLargePrimitiveComponentClassBound

/-! The actual affine-eight subgroup saving pays original actions with
two or three blocks of size eight. Every component's original elementary
translation chart and faithful complement are retained. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.ActualAffineEightSmallTopClassGap
open PrimitiveSocleRawStructure OriginalBlockClassBound

variable {A Ω X : Type} [Group A] [MulAction A Ω] [MulAction A X]
    [Finite A] [Finite Ω] [Finite X] [FaithfulSMul A Ω]

theorem class_cube_le (b : Ω → X)
    (hb : ∀ (a : A) (ω : Ω), b (a • ω) = a • b ω)
    (hblocks : Nat.card X = 2 ∨ Nat.card X = 3)
    (hsize : ∀ x, Nat.card (originalBlockFibre b x) = 8)
    (hprimitive : ∀ x, MulAction.IsPreprimitive
      (originalBlockComponent b hb x) (originalBlockFibre b x))
    (hprofiles : ∀ x, Nonempty (PrimitiveAffineProfile
      (originalBlockComponent b hb x) (originalBlockFibre b x))) :
    Nat.card (ConjClasses A)^3 ≤ 5^(Nat.card Ω-1) := by
  apply SmallTopLargePrimitiveComponentClassBound.class_cube_le_of_subnormal_component_gaps
    b hb 8 (by decide) hblocks hsize
  intro x L _hL
  obtain ⟨P⟩ := hprofiles x
  letI : Nontrivial (originalBlockFibre b x) :=
    Finite.one_lt_card_iff_nontrivial.mp (by rw [hsize]; decide)
  simpa only [hsize x] using
    AffineDegreeEightSubgroupClassGap.subgroup_class_cube_gap P (hprimitive x)
      (Classical.choice inferInstance) (hsize x) L

end SymmetricSubgroupAsymptotics.ActualAffineEightSmallTopClassGap
