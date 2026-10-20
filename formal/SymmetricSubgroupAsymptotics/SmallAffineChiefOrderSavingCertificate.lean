import SymmetricSubgroupAsymptotics.SmallAffineSimpleNormalChiefCertificate
import SymmetricSubgroupAsymptotics.NonabelianMonolithicQuotientChiefSaving

/-! Structural alternatives for the small-affine order saving. A simple
normal subgroup may occur either in the original group or in an actual
monolithic quotient. Neither constructor assumes a chief-series bound. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu

structure SmallAffineMonolithicQuotientChiefCertificate
    (G : Type) [Group G] [Finite G] (cap : ℕ) where
  Target : Type
  [targetGroup : Group Target]
  [targetFinite : Finite Target]
  quotientMap : G →* Target
  quotient_surjective : Function.Surjective quotientMap
  core : Subgroup Target
  [normal : core.Normal]
  noncommutative : ¬ IsMulCommutative core
  le_every_nontrivial_normal : ∀ K : Subgroup Target,
    K.Normal → K ≠ ⊥ → core ≤ K
  order_budget : ArithmeticFunction.cardFactors (Nat.card G) ≤
    ArithmeticFunction.cardFactors (Nat.card core)+cap

inductive SmallAffineChiefOrderSavingCertificate
    (G : Type) [Group G] [Finite G] (cap : ℕ) : Type 1
  | simpleNormal : SmallAffineSimpleNormalChiefCertificate G cap →
      SmallAffineChiefOrderSavingCertificate G cap
  | monolithicQuotient : SmallAffineMonolithicQuotientChiefCertificate G cap →
      SmallAffineChiefOrderSavingCertificate G cap

namespace SmallAffineChiefOrderSavingCertificate

variable {G : Type} [Group G] [Finite G] {cap : ℕ}

theorem chief_bound (C : SmallAffineChiefOrderSavingCertificate G cap)
    (s : ActualChiefSeries G) : actualChiefSeriesAbelianLength s ≤ cap := by
  cases C with
  | simpleNormal C => exact C.chief_bound s
  | monolithicQuotient C =>
    letI : Group C.Target := C.targetGroup
    letI : Finite C.Target := C.targetFinite
    letI : C.core.Normal := C.normal
    have hs := actualChiefSeriesAbelianLength_add_monolithic_quotient_order_le
      s C.quotientMap C.quotient_surjective C.core C.noncommutative
      C.le_every_nontrivial_normal
    have hb := C.order_budget
    omega

end SmallAffineChiefOrderSavingCertificate
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics
