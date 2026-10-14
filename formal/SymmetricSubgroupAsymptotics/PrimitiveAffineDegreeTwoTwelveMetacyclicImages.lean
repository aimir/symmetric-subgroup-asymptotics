import SymmetricSubgroupAsymptotics.TernaryFourBlockMetacyclicModel
import SymmetricSubgroupAsymptotics.FiniteNormalRegistrySocleOfQuotientBounds
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelvePairFiniteCatalogueRows1To50

/-!
# Original quotient socles for rows 38, 39, and 42

The projection I + rotate₂ gives the original simultaneous translations
on opposite ternary blocks. Recentring all four triples at 2 makes the
displayed affine involutions linear. Two actual generator identities per
translation/rotation and one involution identity identify each image with
the original literal top. Every original quotient then inherits the bound
two from the shared coprime metacyclic model.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace PrimitiveAffineDegreeTwoTwelveMetacyclicImages

open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
open DegreeTwoTwelvePairFiniteCatalogue
open TernaryFourBlockMetacyclicModel
open PrimitiveAffineDegreeTwoTwelveRow131AffineModel (Block Vector Translation Points)

def projection : Vector →ₗ[ZMod 3] Vector :=
  LinearMap.id +
    (PrimitiveAffineDegreeTwoTwelveRow131AffineModel.linearAction
      (Multiplicative.ofAdd 2)).toLinearMap

theorem projection_equivariant (reverse negate : Bool)
    (g : Complement reverse) (v : Vector) :
    projection (linearAction reverse negate g v) =
      linearAction reverse negate g (projection v) := by
  have hindex : ∀ (h : Complement reverse) (i : Block),
      blockAction reverse h ((Multiplicative.ofAdd 2 : Block)⁻¹ * i) =
        (Multiplicative.ofAdd 2 : Block)⁻¹ * blockAction reverse h i := by
    cases reverse <;> decide +kernel
  funext i
  change (scalar reverse negate g : ZMod 3) * v (blockAction reverse g⁻¹ i) +
      (scalar reverse negate g : ZMod 3) *
        v (blockAction reverse g⁻¹ ((Multiplicative.ofAdd 2 : Block)⁻¹ * i)) =
    (scalar reverse negate g : ZMod 3) *
      (v (blockAction reverse g⁻¹ i) +
        v ((Multiplicative.ofAdd 2 : Block)⁻¹ * blockAction reverse g⁻¹ i))
  rw [hindex, mul_add]

def projectedModelMap (reverse negate : Bool) : Model reverse negate →* Model reverse negate :=
  SemidirectProduct.map projection.toAddMonoidHom.toMultiplicative
    (MonoidHom.id (Complement reverse)) (by
      intro g
      apply MonoidHom.ext
      intro v
      apply Multiplicative.toAdd.injective
      exact projection_equivariant reverse negate g v.toAdd)

def centeredPointEquiv : Fin 12 ≃ Points :=
  PrimitiveAffineDegreeTwoTwelveRow131AffineModel.pointEquiv.trans
    (PrimitiveAffineDegreeTwoTwelveRow131AffineModel.translations
      (Multiplicative.ofAdd (fun _ : Block ↦ (1 : ZMod 3))))

def literalMap (reverse negate : Bool) : Model reverse negate →* Equiv.Perm (Fin 12) :=
  centeredPointEquiv.symm.permCongrHom.toMonoidHom.comp
    ((TernaryMonomialSemidirect.action (blockAction reverse) (scalar reverse negate)).comp
      (projectedModelMap reverse negate))

section Consumer

variable (reverse negate : Bool) (targetGenerators : Fin 3 → Equiv.Perm (Fin 12))
  (index : Equiv.Perm (Fin 3))
  (hbinding : ∀ i, literalMap reverse negate (generators reverse negate i) =
    targetGenerators (index i))

include reverse negate targetGenerators index hbinding

theorem literalMap_range :
    (literalMap reverse negate).range = Subgroup.closure (Set.range targetGenerators) := by
  let T := Subgroup.closure (Set.range targetGenerators)
  apply le_antisymm
  · have hle : Subgroup.closure (Set.range (generators reverse negate)) ≤
        T.comap (literalMap reverse negate) := by
      apply (Subgroup.closure_le _).mpr
      rintro _ ⟨i, rfl⟩
      change literalMap reverse negate (generators reverse negate i) ∈ T
      rw [hbinding]
      exact Subgroup.subset_closure (Set.mem_range_self (index i))
    rintro _ ⟨g, rfl⟩
    apply hle
    rw [model_generated]
    exact Subgroup.mem_top g
  · apply (Subgroup.closure_le _).mpr
    rintro _ ⟨i, rfl⟩
    refine ⟨generators reverse negate (index.symm i), ?_⟩
    rw [hbinding, index.apply_symm_apply]

def modelToTop : Model reverse negate →* Subgroup.closure (Set.range targetGenerators) :=
  (MulEquiv.subgroupCongr
    (literalMap_range reverse negate targetGenerators index hbinding)).toMonoidHom.comp
      (literalMap reverse negate).rangeRestrict

theorem modelToTop_surjective :
    Function.Surjective (modelToTop reverse negate targetGenerators index hbinding) :=
  (MulEquiv.subgroupCongr
    (literalMap_range reverse negate targetGenerators index hbinding)).surjective.comp
      (literalMap reverse negate).rangeRestrict_surjective

theorem quotientSocle (N : Subgroup (Subgroup.closure (Set.range targetGenerators)))
    [N.Normal] :
    SocleNormalGeneratorBound (Subgroup.closure (Set.range targetGenerators) ⧸ N) 2 :=
  socle_of_surjective reverse negate
    ((QuotientGroup.mk' N).comp (modelToTop reverse negate targetGenerators index hbinding))
    ((QuotientGroup.mk'_surjective N).comp
      (modelToTop_surjective reverse negate targetGenerators index hbinding))

end Consumer

theorem row38_binding (i : Fin 3) :
    literalMap true true (generators true true i) = row38Generators i := by
  apply Equiv.ext
  intro x
  revert i x
  decide +kernel

theorem row39_binding (i : Fin 3) :
    literalMap false true (generators false true i) =
      row39Generators (Equiv.swap 1 2 i) := by
  apply Equiv.ext
  intro x
  revert i x
  decide +kernel

theorem row42_binding (i : Fin 3) :
    literalMap true false (generators true false i) = row42Generators i := by
  apply Equiv.ext
  intro x
  revert i x
  decide +kernel

def row38TopSocle : row38Interface.normalRegistry.QuotientSocleGeneratorFamily 2 :=
  .ofQuotientBounds _ (fun N ↦ by
    letI := N.2
    exact quotientSocle true true row38Generators (Equiv.refl _) row38_binding N.1)

def row39TopSocle : row39Interface.normalRegistry.QuotientSocleGeneratorFamily 2 :=
  .ofQuotientBounds _ (fun N ↦ by
    letI := N.2
    exact quotientSocle false true row39Generators (Equiv.swap 1 2) row39_binding N.1)

def row42TopSocle : row42Interface.normalRegistry.QuotientSocleGeneratorFamily 2 :=
  .ofQuotientBounds _ (fun N ↦ by
    letI := N.2
    exact quotientSocle true false row42Generators (Equiv.refl _) row42_binding N.1)

end PrimitiveAffineDegreeTwoTwelveMetacyclicImages
end SymmetricSubgroupAsymptotics

end
