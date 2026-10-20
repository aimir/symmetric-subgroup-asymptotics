import SymmetricSubgroupAsymptotics.SmallAffineChiefOrderSavingCertificate
import Mathlib.GroupTheory.Solvable

/-! Structural order-saving certificates also certify nonsolubility.
Their numerical budget is irrelevant to this implication. -/
set_option autoImplicit false
noncomputable section
open scoped commutatorElement
namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu

namespace SmallAffineChiefOrderSavingCertificate

variable {G : Type} [Group G] [Finite G] {cap : ℕ}

theorem not_isSolvable (C : SmallAffineChiefOrderSavingCertificate G cap) :
    ¬ IsSolvable G := by
  intro hG
  letI : IsSolvable G := hG
  cases C with
  | simpleNormal C =>
    letI : IsSimpleGroup C.core := C.simple
    have hE : IsSolvable C.core := inferInstance
    apply C.noncommutative
    exact ⟨⟨IsSimpleGroup.comm_iff_isSolvable.mpr hE⟩⟩
  | monolithicQuotient C =>
    letI : Group C.Target := C.targetGroup
    letI : Finite C.Target := C.targetFinite
    letI : C.core.Normal := C.normal
    letI : IsSolvable C.Target :=
      solvable_of_surjective (f := C.quotientMap) C.quotient_surjective
    have hcomm : ⁅C.core,C.core⁆ ≠ ⊥ := by
      intro h
      apply C.noncommutative
      refine ⟨⟨?_⟩⟩
      intro x y
      apply Subtype.ext
      have hx := (Subgroup.commutator_eq_bot_iff_le_centralizer.mp h) x.property
      exact ((Subgroup.mem_centralizer_iff.mp hx) y y.property).symm
    have hE : C.core ≠ ⊥ := by
      intro h
      apply hcomm
      rw [h,Subgroup.commutator_bot_left]
    have hlt : ⁅C.core,C.core⁆ < C.core :=
      IsSolvable.commutator_lt_of_ne_bot hE
    have hle : C.core ≤ ⁅C.core,C.core⁆ :=
      C.le_every_nontrivial_normal _ (Subgroup.commutator_normal C.core C.core) hcomm
    exact (not_le_of_gt hlt) hle

end SmallAffineChiefOrderSavingCertificate
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics
