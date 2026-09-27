import SymmetricSubgroupAsymptotics.BinaryAdditiveTwoOrbitChart
import SymmetricSubgroupAsymptotics.BinaryFourTranslationMoments

/-! The additive chart's first parity is an original orbit sum.

The first block is proved to be one entire original H-orbit from the
actual surjective translation coordinate. Consequently its four-label
sum equals the sum on the literal original orbit subtype, independently
of the auxiliary regular-coordinate choice.
-/
set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics.BinaryAdditiveTwoOrbitChart

variable {G X : Type} [Group G] [MulAction G X]
    (H : Subgroup G) (C : BinaryAdditiveTwoOrbitChart (X := X) H)

def leftOrbit : MulAction.orbitRel.Quotient H X :=
  Quotient.mk'' (C.chart (Sum.inl 0))

theorem chart_left_mem_orbit (v : BinaryRegularFourSpace) :
    C.chart (Sum.inl v)∈(leftOrbit H C).orbit := by
  change C.chart (Sum.inl v)∈MulAction.orbit H (C.chart (Sum.inl 0))
  obtain ⟨h,hh⟩ := C.coordinate_surjective v
  change C.coordinate h=v at hh
  apply MulAction.mem_orbit_iff.mpr
  refine ⟨h,?_⟩
  change (h:G) • C.chart (Sum.inl 0)=C.chart (Sum.inl v)
  rw [C.normal_left,add_zero,hh]

/-- An equivalence onto the literal original orbit, retaining each
original point as its value. -/
def leftOrbitEquiv : BinaryRegularFourSpace ≃ (leftOrbit H C).orbit :=
  Equiv.ofBijective (fun v => ⟨C.chart (Sum.inl v),chart_left_mem_orbit H C v⟩) ⟨by
    intro v w he
    exact Sum.inl.inj (C.chart.injective (congrArg Subtype.val he)),by
    intro x
    have hx : x.val∈MulAction.orbit H (C.chart (Sum.inl 0)) := x.property
    obtain ⟨h,hh⟩ := MulAction.mem_orbit_iff.mp hx
    refine ⟨C.coordinate h,Subtype.ext ?_⟩
    change (h:G) • C.chart (Sum.inl 0)=x.val at hh
    rw [C.normal_left,add_zero] at hh
    exact hh⟩

@[simp] theorem leftOrbitEquiv_val (v : BinaryRegularFourSpace) :
    (leftOrbitEquiv H C v).val=C.chart (Sum.inl v) := rfl

/-- No multiplicity or factorial is introduced by the additive labels. -/
theorem first_parity_eq_orbitSum [Finite X] (f : X → ZMod 2) :
    BinaryTranslationMoments.parity (BinaryTranslationMoments.leftFunction C.chart f)=
      PermutationBinaryTwoOrbitSplit.orbitSum H (leftOrbit H C) f := by
  letI : Fintype X := Fintype.ofFinite X
  simpa only [BinaryTranslationMoments.parity,BinaryTranslationMoments.leftFunction,
    PermutationBinaryTwoOrbitSplit.orbitSum,LinearMap.coe_mk,AddHom.coe_mk,
    leftOrbitEquiv_val] using
    (Equiv.sum_comp (leftOrbitEquiv H C) (fun x => f x.val))

end SymmetricSubgroupAsymptotics.BinaryAdditiveTwoOrbitChart
