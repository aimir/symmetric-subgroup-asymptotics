import SymmetricSubgroupAsymptotics.OriginalTwoBlockPrimitiveFrame
import SymmetricSubgroupAsymptotics.NormalGeneratorQuotientSocles

/-! Actual two-block actions with primitive eight-point components have
three-generator socles in every original quotient. The local singleton
normal-generation theorem is obtained from the bare degree-eight
classification, including its four nonaffine primitive actions. No finite
list of two-block extensions is assumed. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.OriginalMinimalBlock
open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer

variable {G X : Type} [Group G] [Finite G] [MulAction G X]
  [MulAction.IsPretransitive G X] [FaithfulSMul G X] [Finite X]
  {x : X} (D : OriginalMinimalBlock (A := G) x)

/-- The actual group, quotient denominator and local primitive action are
unchanged throughout the two-block normal-generation argument. -/
theorem twoPrimitiveEight_quotient_socle_three
    (published : DegreeEightCanonicalCatalogue.PublishedClassification)
    (hf : Nat.card D.Fibre = 8) (hi : Nat.card D.Points = 2)
    (N : Subgroup G) [N.Normal] : SocleNormalGeneratorBound (G ⧸ N) 3 := by
  have hall : ∀ M : Subgroup G, M.Normal →
      ∃ z : Fin 3 → G, Subgroup.normalClosure (Set.range z) = M := by
    simpa only [show 1 + 1 + 1 = 3 from rfl] using
      D.twoBlock_normal_generating_tuples hi
        (D.eightPoint_component_normal_singletons published hf)
  exact normal_generating_tuples_of_surjective (QuotientGroup.mk' N)
    (QuotientGroup.mk'_surjective N) hall (finiteGroupSocle _) inferInstance

end SymmetricSubgroupAsymptotics.OriginalMinimalBlock
