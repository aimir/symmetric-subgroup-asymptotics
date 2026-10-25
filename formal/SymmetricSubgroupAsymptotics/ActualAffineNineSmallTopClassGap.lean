import SymmetricSubgroupAsymptotics.AffineDegreeNineSubgroupClassGap
import SymmetricSubgroupAsymptotics.SmallTopLargePrimitiveComponentClassBound

/-! The actual affine-nine subgroup saving pays every original action
with two or three blocks of size nine. The literal component profiles
supply their own regular kernels and faithful complements; neither
splitting of the ambient action nor a class-count hypothesis is assumed. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.ActualAffineNineSmallTopClassGap
open PrimitiveSocleRawStructure OriginalBlockClassBound

variable {A Ω X : Type} [Group A] [MulAction A Ω] [MulAction A X]
    [Finite A] [Finite Ω] [Finite X] [FaithfulSMul A Ω]

theorem class_cube_le (b : Ω → X)
    (hb : ∀ (a : A) (ω : Ω), b (a • ω) = a • b ω)
    (hblocks : Nat.card X = 2 ∨ Nat.card X = 3)
    (hsize : ∀ x, Nat.card (originalBlockFibre b x) = 9)
    (hprofiles : ∀ x, Nonempty (PrimitiveAffineProfile
      (originalBlockComponent b hb x) (originalBlockFibre b x))) :
    Nat.card (ConjClasses A)^3 ≤ 5^(Nat.card Ω-1) := by
  apply SmallTopLargePrimitiveComponentClassBound.class_cube_le_of_subnormal_component_gaps
    b hb 9 (by decide) hblocks hsize
  intro x L _hL
  obtain ⟨P⟩ := hprofiles x
  letI : Nontrivial (originalBlockFibre b x) :=
    Finite.one_lt_card_iff_nontrivial.mp (by rw [hsize]; decide)
  simpa only [hsize x] using
    AffineDegreeNineSubgroupClassGap.subgroup_class_cube_gap P
      (Classical.choice inferInstance) (hsize x) L

end SymmetricSubgroupAsymptotics.ActualAffineNineSmallTopClassGap
