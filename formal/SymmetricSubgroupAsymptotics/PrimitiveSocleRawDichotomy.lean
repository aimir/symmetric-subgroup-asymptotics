import SymmetricSubgroupAsymptotics.PrimitiveSocleRawProfile
import SymmetricSubgroupAsymptotics.PrimitiveCatalogueClassificationPublished

/-! Bind raw ordinary classification to both actual actions requested by
the existing primitive catalogue owner. Every quantitative profile is
constructed internally; no catalogue capacity is a raw hypothesis. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.PrimitiveSocleRawStructure
open Non2UnipotentPrefixFiniteMenu

/-- Generic faithful primitive-action consumer. -/
def PublishedONanScottStructure.actionDichotomy
    (raw : PublishedONanScottStructure) (hindex : PublishedSimpleIndexBounds)
    (G X : Type) [Group G] [Finite G] [Finite X] [MulAction G X]
    [FaithfulSMul G X] [Nontrivial X] [MulAction.IsPreprimitive G X] :
    ExactPrimitiveSemisimpleOuterLogProfile G (Nat.card X) ⊕
      PrimitiveAffineProfile G X :=
  match Classical.choice (raw G X) with
  | .inl D => .inl (D.exactProfile hindex)
  | .inr A => .inr A

/-- The former quantitative O'Nan--Scott interface is a theorem of the raw
structural classification and the separate simple-index inequalities. -/
def PublishedONanScottStructure.toSocleDichotomy
    (raw : PublishedONanScottStructure) (hindex : PublishedSimpleIndexBounds) :
    PublishedPrimitiveSocleDichotomyInput where
  primitive := by
    intro w U hw hp
    letI : Nontrivial (Fin w) := Fin.nontrivial_iff_two_le.mpr (by omega)
    letI : MulAction.IsPreprimitive (preE7NonPairAction w U) (Fin w) := hp
    simpa only [Nat.card_fin] using
      raw.actionDichotomy hindex (preE7NonPairAction w U) (Fin w)
  imprimitive := by
    intro w U hw basePoint block
    letI : Nontrivial block.Fibre :=
      Finite.one_lt_card_iff_nontrivial.mp (by
        have := block.degrees_ge_two.1
        omega)
    letI : MulAction.IsPreprimitive block.Component block.Fibre :=
      block.component_preprimitive
    exact raw.actionDichotomy hindex block.Component block.Fibre

end SymmetricSubgroupAsymptotics.PrimitiveSocleRawStructure
