import SymmetricSubgroupAsymptotics.SixPairAction147PrimitiveB6Pilot
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoSixPairAction147ClassBase

/-! The structural pilot and the existing literal table-action147 have
the same original generator tuple. No conjugacy, normal-list, abstract
order, or class-cover certificate is used to identify this source. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.SixPairAction147PrimitiveB6LiteralBinding

abbrev literalOriginal : Subgroup (Equiv.Perm (Fin 12)) :=
  Subgroup.closure (Set.range PrimitiveAffineDegreeTwoSixPairAction147ClassPilot.generators)

theorem generators_eq : SixPairAction147PrimitiveB6Pilot.generators=
    PrimitiveAffineDegreeTwoSixPairAction147ClassPilot.generators := by
  funext j
  apply Equiv.ext
  intro i
  revert j i
  decide +kernel

theorem original_eq : SixPairAction147PrimitiveB6Pilot.Original=literalOriginal := by
  exact congrArg (fun gs : Fin 2 → Equiv.Perm (Fin 12) => Subgroup.closure (Set.range gs))
    generators_eq

/-- Complete all-normal source on the existing stored literal subgroup. -/
def actionCertificate (h6 : PublishedPrimitiveDegreeSixClassification)
    (hZmud : ZmudFaithfulCharacterTupleInput) :
    Non2UnipotentPrefixFiniteMenu.PreE7B6ActionCertificate literalOriginal :=
  original_eq ▸ SixPairAction147PrimitiveB6Pilot.actionCertificate h6 hZmud

end SymmetricSubgroupAsymptotics.SixPairAction147PrimitiveB6LiteralBinding
