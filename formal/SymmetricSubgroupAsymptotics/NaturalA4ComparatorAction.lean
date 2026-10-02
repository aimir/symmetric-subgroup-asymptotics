import SymmetricSubgroupAsymptotics.ScalarFourHeadDefinitions

/-! # The regular C3 comparator on three labelled points -/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace NaturalA4RankTail

private noncomputable def c3PointEquiv : CyclicThree ≃ Fin 3 :=
  Fintype.equivFin CyclicThree

/-- The regular `C3` comparator on three labelled points. -/
def comparatorAction : CyclicThree →* Equiv.Perm (Fin 3) :=
  c3PointEquiv.permCongrHom.toMonoidHom.comp
    (MulAction.toPermHom CyclicThree CyclicThree)

theorem comparatorAction_injective : Function.Injective comparatorAction :=
  c3PointEquiv.permCongrHom.injective.comp MulAction.toPerm_injective

end NaturalA4RankTail
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
