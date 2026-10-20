import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveRow131QuotientSocles

/-!
# Literal images of an equivariant map on the row-131 translations

A linear endomorphism commuting with the displayed C4 action induces an
endomorphism of the actual semidirect model. Binding its two generator
images to an original literal tuple proves that the image is exactly
that top. Every original normal quotient then has a one-generator socle.
Only an actual equivariance proof and two point-action equalities are
inputs; no assertion about the target socle is assumed.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace PrimitiveAffineDegreeTwoTwelveRow131ImageSocles

open PrimitiveAffineDegreeTwoTwelveRow131AffineModel
open SemidirectProduct

variable (P : Vector →ₗ[ZMod 3] Vector)
  (hP : ∀ c v, P (linearAction c v) = linearAction c (P v))

def modelMap : Model →* Model :=
  SemidirectProduct.map P.toAddMonoidHom.toMultiplicative (MonoidHom.id Block) (by
    intro c
    apply MonoidHom.ext
    intro v
    apply Multiplicative.toAdd.injective
    exact hP c v.toAdd)

def literalMap : Model →* Equiv.Perm (Fin 12) := literalAction.comp (modelMap P hP)

variable (generators : Fin 2 → Equiv.Perm (Fin 12))
  (hbinding : ∀ i, literalMap P hP (modelGenerators i) = generators i)

include P hP generators hbinding

theorem literalMap_range :
    (literalMap P hP).range = Subgroup.closure (Set.range generators) := by
  let T : Subgroup (Equiv.Perm (Fin 12)) := Subgroup.closure (Set.range generators)
  apply le_antisymm
  · have hle : Subgroup.closure (Set.range modelGenerators) ≤ T.comap (literalMap P hP) := by
      apply (Subgroup.closure_le _).mpr
      rintro _ ⟨i, rfl⟩
      change literalMap P hP (modelGenerators i) ∈ T
      rw [hbinding]
      exact Subgroup.subset_closure (Set.mem_range_self i)
    rintro _ ⟨g, rfl⟩
    apply hle
    rw [model_generated]
    exact Subgroup.mem_top g
  · apply (Subgroup.closure_le _).mpr
    rintro _ ⟨i, rfl⟩
    exact ⟨modelGenerators i, hbinding i⟩

def modelToTop : Model →* Subgroup.closure (Set.range generators) :=
  (MulEquiv.subgroupCongr (literalMap_range P hP generators hbinding)).toMonoidHom.comp
    (literalMap P hP).rangeRestrict

theorem modelToTop_surjective : Function.Surjective (modelToTop P hP generators hbinding) :=
  (MulEquiv.subgroupCongr (literalMap_range P hP generators hbinding)).surjective.comp
    (literalMap P hP).rangeRestrict_surjective

def originalTopMap : Top →* Subgroup.closure (Set.range generators) :=
  (modelToTop P hP generators hbinding).comp modelEquiv.symm.toMonoidHom

theorem originalTopMap_surjective :
    Function.Surjective (originalTopMap P hP generators hbinding) :=
  (modelToTop_surjective P hP generators hbinding).comp modelEquiv.symm.surjective

theorem socle_of_surjective {Q : Type} [Group Q]
    (pi : Subgroup.closure (Set.range generators) →* Q) (hpi : Function.Surjective pi) :
    SocleNormalGeneratorBound Q 1 :=
  PrimitiveAffineDegreeTwoTwelveRow131AffineModel.socle_of_surjective
    (pi.comp (originalTopMap P hP generators hbinding))
    (hpi.comp (originalTopMap_surjective P hP generators hbinding))

theorem quotientSocle (N : Subgroup (Subgroup.closure (Set.range generators))) [N.Normal] :
    SocleNormalGeneratorBound (Subgroup.closure (Set.range generators) ⧸ N) 1 :=
  socle_of_surjective P hP generators hbinding
    (QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N)

end PrimitiveAffineDegreeTwoTwelveRow131ImageSocles
end SymmetricSubgroupAsymptotics

end
