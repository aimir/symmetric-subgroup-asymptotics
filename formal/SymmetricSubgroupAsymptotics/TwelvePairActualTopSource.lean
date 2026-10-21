import SymmetricSubgroupAsymptotics.PrimitiveTwelvePairActualSource
import SymmetricSubgroupAsymptotics.TwelvePointQuotientSocleTwoEpimorphisms
import SymmetricSubgroupAsymptotics.BinaryPairFrameTransport
import SymmetricSubgroupAsymptotics.SquarefreeGroupSocleOne

/-! Direct twelve-pair source branches on the SAME actual pair frame.
The top may be primitive, cyclic-by-cyclic, or a Z-group. Every normal axis
of the original24-point group is aggregated by the existing exact kernel
and top-quotient chart. No point locator or model recognition is an input. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.TwelvePairActualTopSource
open Non2UnipotentPrefixFiniteMenu PrimitiveSocleRawStructure
open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer

variable (p : PreE7PairActionClass 12)
    (F : BinaryPairFrame (preE7PairAction 12 p) (Fin 12))

/-- The quotient capacity is allowed two slots while the actual natural
module costs four: the full top-map envelope still fits the width24 gap. -/
def source_of_quotientSocle_two
    (hZmud : ZmudFaithfulCharacterTupleInput) (lit : PreE7CharacterLiterature)
    (hSocle : ∀ (M : Subgroup F.top.range) [M.Normal],
      SocleNormalGeneratorBound (F.top.range ⧸ M) 2) :
    PreE7RankTailSourceOrYonedaTopData 24
      (preE7SmallPairNonPairAction 12 (by decide) p) := by
  letI : MulAction.IsPretransitive F.top.range (Fin 12) := F.top_pretransitive
  have ht : Nat.card F.top.range ≤ 2^29 := degreeTwelve_group_order_le
  exact TwelvePairOriginalSource.source p F ht (403/150)
    (by norm_num [halfDegree,preE7CharacterRho])
    (fun N _ b => TwelvePairActualKernelQuotientSum.quotient_sum_le F ht
      PrimitiveTwelvePairActualSource.natural_uniform
      (fun M _ b J => TwelvePointQuotientSocleTwoEpimorphisms.quotient_epi_le
        hZmud lit hSocle M b J) N b)

/-- A complete proved branch for arbitrary actual cyclic-by-cyclic tops.
The cyclic kernel need not split and the action is not replaced by a model. -/
def source_of_cyclicByCyclic
    (hZmud : ZmudFaithfulCharacterTupleInput) (lit : PreE7CharacterLiterature)
    (E : Subgroup F.top.range) [E.Normal] [IsCyclic E]
    [IsCyclic (F.top.range ⧸ E)] :
    PreE7RankTailSourceOrYonedaTopData 24
      (preE7SmallPairNonPairAction 12 (by decide) p) :=
  source_of_quotientSocle_two p F hZmud lit
    (fun M _ => TwelvePointQuotientSocleTwoEpimorphisms.cyclicByCyclic_quotient_socle_two E M)

/-- Z-groups have cyclic actual socles in all their actual quotients. -/
def source_of_isZGroup [IsZGroup F.top.range]
    (hZmud : ZmudFaithfulCharacterTupleInput) (lit : PreE7CharacterLiterature) :
    PreE7RankTailSourceOrYonedaTopData 24
      (preE7SmallPairNonPairAction 12 (by decide) p) := by
  apply source_of_quotientSocle_two p F hZmud lit
  intro M _
  letI : IsZGroup (F.top.range ⧸ M) :=
    IsZGroup.of_surjective (f := QuotientGroup.mk' M) (QuotientGroup.mk'_surjective M)
  exact (socleNormalGeneratorBound_one_of_isZGroup (G := F.top.range ⧸ M)).mono (by decide)

/-- The primitive branch was already proved by the generic actual
nonaffine quotient envelope, with no C336 or twelve-point locator. -/
def source_of_primitive [MulAction.IsPreprimitive F.top.range (Fin 12)]
    (hindex : PublishedSimpleIndexBounds)
    (hZmud : ZmudFaithfulCharacterTupleInput) (lit : PreE7CharacterLiterature)
    (hMN : PermutationSubgroupGeneratorBound) :
    PreE7RankTailSourceOrYonedaTopData 24
      (preE7SmallPairNonPairAction 12 (by decide) p) :=
  PrimitiveTwelvePairActualSource.source p F hindex hZmud lit hMN

end SymmetricSubgroupAsymptotics.TwelvePairActualTopSource
