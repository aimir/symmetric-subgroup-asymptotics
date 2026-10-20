import SymmetricSubgroupAsymptotics.SixPairPrimitiveRepresentativeSource
import SymmetricSubgroupAsymptotics.PrimitiveSixTwelveNormalConsumerFacts
import Mathlib.Tactic.FinCases
import SymmetricSubgroupAsymptotics.PrimitiveSixPublishedCycleWitnessBoundedCatalogueReduced

/-! Isolated actual degree6/12 normal-consumer route. Original records,
finite index sets and all certificate declarations are imported unchanged. -/
set_option autoImplicit false

noncomputable section

open scoped Classical

namespace SymmetricSubgroupAsymptotics.SixPairPrimitiveRepresentativeSource

namespace BoundedCatalogueReduced

open Non2UnipotentPrefixFiniteMenu

variable (socle : PublishedPrimitiveSocleDichotomyInput)
  (catalogue : PrimitiveSixTwelveNormalConsumerFacts)
  (h6 : PublishedPrimitiveDegreeSixClassification) (hZmud : ZmudFaithfulCharacterTupleInput)

def actionCertificate {U : Subgroup (Equiv.Perm (Fin 12))}
    (F : BinaryPairFrame U (Fin 6)) [MulAction.IsPreprimitive F.top.range (Fin 6)] :
    PreE7B6ActionCertificate U := by
  apply Classical.choice
  obtain ⟨g,c,hc⟩ := _root_.SymmetricSubgroupAsymptotics.PrimitiveSixPublishedCycleWitness.BoundedCatalogueReduced.exists_original_point_conjugacy
    socle catalogue F.top.range
  obtain ⟨a,ha⟩ := F.top.rangeRestrict_surjective g
  let E := F.reindex c
  have he : E.top a=SixPointFiveCyclePrimitive.cycle := by
    have hag : F.top a=g.val := congrArg Subtype.val ha
    change c.permCongrHom (F.top a)=_
    rw [hag]
    exact hc
  obtain ⟨b,hb⟩ := MulAction.exists_smul_eq F.top.range (c.symm 5) (c.symm 0)
  obtain ⟨u,hu⟩ := F.top.rangeRestrict_surjective b
  have hmove : E.top u 5≠5 := by
    have hub : F.top u=b.val := congrArg Subtype.val hu
    change c (F.top u (c.symm 5))≠5
    rw [hub,show b.val (c.symm 5)=c.symm 0 from hb,c.apply_symm_apply]
    decide
  exact ⟨SixPairFiveCycleUniversalPolynomial.actionCertificate E h6 hZmud a u he hmove⟩

def source (p : PreE7PairActionClass 6)
    (F : BinaryPairFrame (preE7PairAction 6 p) (Fin 6))
    [hprimitive : MulAction.IsPreprimitive F.top.range (Fin 6)] :
    PreE7RankTailSourceOrYonedaTopData 12 (preE7SixPairNonPairAction p) :=
  .inl (.b6 (@_root_.SymmetricSubgroupAsymptotics.SixPairPrimitiveRepresentativeSource.BoundedCatalogueReduced.actionCertificate socle catalogue h6 hZmud
    (preE7PairAction 6 p) F hprimitive))

end BoundedCatalogueReduced

end SymmetricSubgroupAsymptotics.SixPairPrimitiveRepresentativeSource

