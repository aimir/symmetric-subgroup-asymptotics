import SymmetricSubgroupAsymptotics.QuaternaryTripleTernaryWreathModel
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelvePairFiniteCatalogueRows51To100

/-! The original row94 tuple is the displayed regular action on three
four-point blocks. The chart sends cell `i`, position `j` to
`2 + 4i + 3j` modulo twelve. The exact generator binding and symbolic
generation of the wreath model identify the original image range. -/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace PrimitiveAffineDegreeTwoTwelveRow94WreathModel

open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
open DegreeTwoTwelvePairFiniteCatalogue QuaternaryTripleTernaryWreathModel

def pointEquiv : Fin 12 ≃ Points where
  toFun := ![(Multiplicative.ofAdd 1, 2), (Multiplicative.ofAdd 2, 1),
    (Multiplicative.ofAdd 0, 0), (Multiplicative.ofAdd 1, 3),
    (Multiplicative.ofAdd 2, 2), (Multiplicative.ofAdd 0, 1),
    (Multiplicative.ofAdd 1, 0), (Multiplicative.ofAdd 2, 3),
    (Multiplicative.ofAdd 0, 2), (Multiplicative.ofAdd 1, 1),
    (Multiplicative.ofAdd 2, 0), (Multiplicative.ofAdd 0, 3)]
  invFun p := (#[2, 5, 8, 11, 6, 9, 0, 3, 10, 1, 4, 7] : Array (Fin 12))[
    4 * p.1.toAdd.val + p.2.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def literalAction : Model →* Equiv.Perm (Fin 12) :=
  pointEquiv.symm.permCongrHom.toMonoidHom.comp modelAction

theorem generators_binding (i : Fin 2) :
    literalAction (modelGenerators i) = row94Generators i := by
  apply Equiv.ext
  intro x
  revert i x
  decide +kernel

theorem literalAction_range : literalAction.range = Row94Top := by
  apply le_antisymm
  · have hle : Subgroup.closure (Set.range modelGenerators) ≤ Row94Top.comap literalAction := by
      apply (Subgroup.closure_le _).mpr
      rintro _ ⟨i, rfl⟩
      change literalAction (modelGenerators i) ∈ Row94Top
      rw [generators_binding]
      exact Subgroup.subset_closure (Set.mem_range_self i)
    rintro _ ⟨g, rfl⟩
    apply hle
    rw [model_generated]
    exact Subgroup.mem_top g
  · apply (Subgroup.closure_le _).mpr
    rintro _ ⟨i, rfl⟩
    exact ⟨modelGenerators i, generators_binding i⟩

def modelToTop : Model →* Row94Top :=
  (MulEquiv.subgroupCongr literalAction_range).toMonoidHom.comp literalAction.rangeRestrict

theorem modelToTop_surjective : Function.Surjective modelToTop :=
  (MulEquiv.subgroupCongr literalAction_range).surjective.comp literalAction.rangeRestrict_surjective

/-- The arbitrary input quotient map remains the map from the original
literal top; only its source is covered by the explicit wreath model. -/
theorem socle_of_surjective {Q : Type} [Group Q] (pi : Row94Top →* Q)
    (hpi : Function.Surjective pi) : SocleNormalGeneratorBound Q 1 :=
  QuaternaryTripleTernaryWreathModel.socle_of_surjective
    (pi.comp modelToTop) (hpi.comp modelToTop_surjective)

theorem quotientSocle (N : Subgroup Row94Top) [N.Normal] :
    SocleNormalGeneratorBound (Row94Top ⧸ N) 1 :=
  socle_of_surjective (QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N)

def topSocle : row94Interface.normalRegistry.QuotientSocleGeneratorFamily 1 :=
  .ofQuotientBounds _ (fun N => by
    letI := N.2
    exact quotientSocle N.1)

end PrimitiveAffineDegreeTwoTwelveRow94WreathModel
end SymmetricSubgroupAsymptotics

end
