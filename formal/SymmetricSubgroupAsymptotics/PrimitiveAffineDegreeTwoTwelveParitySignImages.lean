import SymmetricSubgroupAsymptotics.TernaryFourBlockParityGeneration
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveMetacyclicImages
import SymmetricSubgroupAsymptotics.GeneratedLiteralImage
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelvePairFiniteCatalogueRows51To100
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelvePairFiniteCatalogueRows101To150

/-! Exact signed-block image maps for original rows 79, 81, and 125.
The source models, original twelve points, and original normal quotient
denominators are retained. No finite normal-subgroup registry is added. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace PrimitiveAffineDegreeTwoTwelveParitySignImages

open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
open DegreeTwoTwelvePairFiniteCatalogue
open PrimitiveAffineDegreeTwoTwelveRow131AffineModel (Block)
open BinaryPermutationSemidirectNormalGenerators (Vector cyclicLabels dihedralLabels)
open TernaryFourBlockParityModels
open TernaryFourBlockParityGeneration

section LiteralMap

variable {R : Type} [Group R]
  (p : R →* Equiv.Perm (Fin 2)) (b : R →* Equiv.Perm Block)
  (hlabel : ∀ g i, label (b g i) = p g (label i))
  (q : Vector →ₗ[ZMod 2] Vector)
  (hq : ∀ g v, q (BinaryPermutationSemidirectNormalGenerators.linearAction p g v) =
    BinaryPermutationSemidirectNormalGenerators.linearAction p g (q v))
  (hopposite : ∀ g i, b g ((Multiplicative.ofAdd 2 : Block)⁻¹ * i) =
    (Multiplicative.ofAdd 2 : Block)⁻¹ * b g i)

include hopposite in
theorem projection_equivariant (g : TernaryParitySignModel.Complement p) (v : Block → ZMod 3) :
    PrimitiveAffineDegreeTwoTwelveMetacyclicImages.projection
        (TernaryParitySignModel.linearAction p b label hlabel q hq g v) =
      TernaryParitySignModel.linearAction p b label hlabel q hq g
        (PrimitiveAffineDegreeTwoTwelveMetacyclicImages.projection v) := by
  have hlabelOpp : ∀ i : Block, label ((Multiplicative.ofAdd 2 : Block)⁻¹ * i) = label i := by
    decide +kernel
  funext i
  change TernaryParitySignModel.signs p label q g i * v (b g.right⁻¹ i) +
      TernaryParitySignModel.signs p label q g ((Multiplicative.ofAdd 2 : Block)⁻¹ * i) *
        v (b g.right⁻¹ ((Multiplicative.ofAdd 2 : Block)⁻¹ * i)) =
    TernaryParitySignModel.signs p label q g i *
      (v (b g.right⁻¹ i) + v ((Multiplicative.ofAdd 2 : Block)⁻¹ * b g.right⁻¹ i))
  have hsign : TernaryParitySignModel.signs p label q g
      ((Multiplicative.ofAdd 2 : Block)⁻¹ * i) = TernaryParitySignModel.signs p label q g i :=
    congrArg (fun j ↦ TernaryParitySignModel.coefficient q j g.left) (hlabelOpp i)
  rw [hsign, hopposite, mul_add]

def projectedModelMap : TernaryParitySignModel.Model p b label hlabel q hq →*
    TernaryParitySignModel.Model p b label hlabel q hq :=
  SemidirectProduct.map
    PrimitiveAffineDegreeTwoTwelveMetacyclicImages.projection.toAddMonoidHom.toMultiplicative
    (MonoidHom.id (TernaryParitySignModel.Complement p)) (by
      intro g
      apply MonoidHom.ext
      intro v
      apply Multiplicative.toAdd.injective
      exact projection_equivariant p b hlabel q hq hopposite g v.toAdd)

def literalMap : TernaryParitySignModel.Model p b label hlabel q hq →* Equiv.Perm (Fin 12) :=
  PrimitiveAffineDegreeTwoTwelveMetacyclicImages.centeredPointEquiv.symm.permCongrHom.toMonoidHom.comp
    ((TernaryParitySignModel.action p b label hlabel q hq).comp
      (projectedModelMap p b hlabel q hq hopposite))

end LiteralMap

theorem cyclic_opposite (g i : Block) :
    cyclicBlockAction g ((Multiplicative.ofAdd 2 : Block)⁻¹ * i) =
      (Multiplicative.ofAdd 2 : Block)⁻¹ * cyclicBlockAction g i := by
  revert g i
  decide +kernel

theorem dihedral_opposite (g : TernaryFourBlockMetacyclicModel.Complement true) (i : Block) :
    TernaryFourBlockMetacyclicModel.blockAction true g ((Multiplicative.ofAdd 2 : Block)⁻¹ * i) =
      (Multiplicative.ofAdd 2 : Block)⁻¹ * TernaryFourBlockMetacyclicModel.blockAction true g i := by
  revert g i
  decide +kernel

def row79Map := literalMap cyclicLabels cyclicBlockAction cyclic_label
  LinearMap.id (fun _ _ ↦ rfl) cyclic_opposite

def row81Map := literalMap dihedralLabels (TernaryFourBlockMetacyclicModel.blockAction true)
  dihedral_label sumProjection (sumProjection_equivariant dihedralLabels) dihedral_opposite

def row125Map := literalMap dihedralLabels (TernaryFourBlockMetacyclicModel.blockAction true)
  dihedral_label LinearMap.id (fun _ _ ↦ rfl) dihedral_opposite

theorem row79_binding (i : Fin 3) :
    row79Map (cyclicGenerators i) = row79Generators (Equiv.swap 1 2 i) := by
  apply Equiv.ext
  intro x
  revert i x
  decide +kernel

theorem row81_binding (i : Fin 4) :
    row81Map (dihedralGenerators sumProjection (sumProjection_equivariant dihedralLabels) i) =
      row81Generators (Equiv.swap 1 2 i) := by
  apply Equiv.ext
  intro x
  revert i x
  decide +kernel

theorem row125_binding (i : Fin 4) :
    row125Map (dihedralGenerators LinearMap.id (fun _ _ ↦ rfl) i) =
      row125Generators (Equiv.swap 1 2 i) := by
  apply Equiv.ext
  intro x
  revert i x
  decide +kernel

def row79ToTop : CyclicAffine →* Row79Top :=
  GeneratedLiteralImage.toTop row79Map cyclicGenerators row79Generators
    (Equiv.swap 1 2) TernaryFourBlockParityGeneration.cyclic_generated row79_binding

theorem row79ToTop_surjective : Function.Surjective row79ToTop :=
  GeneratedLiteralImage.toTop_surjective row79Map cyclicGenerators row79Generators
    (Equiv.swap 1 2) TernaryFourBlockParityGeneration.cyclic_generated row79_binding

def row81ToTop : DihedralAffine sumProjection (sumProjection_equivariant dihedralLabels) →* Row81Top :=
  GeneratedLiteralImage.toTop row81Map
    (dihedralGenerators sumProjection (sumProjection_equivariant dihedralLabels)) row81Generators
    (Equiv.swap 1 2)
    (TernaryFourBlockParityGeneration.dihedral_generated sumProjection (sumProjection_equivariant dihedralLabels))
    row81_binding

theorem row81ToTop_surjective : Function.Surjective row81ToTop :=
  GeneratedLiteralImage.toTop_surjective row81Map
    (dihedralGenerators sumProjection (sumProjection_equivariant dihedralLabels)) row81Generators
    (Equiv.swap 1 2)
    (TernaryFourBlockParityGeneration.dihedral_generated sumProjection (sumProjection_equivariant dihedralLabels))
    row81_binding

def row125ToTop : DihedralAffine LinearMap.id (fun _ _ ↦ rfl) →* Row125Top :=
  GeneratedLiteralImage.toTop row125Map
    (dihedralGenerators LinearMap.id (fun _ _ ↦ rfl)) row125Generators (Equiv.swap 1 2)
    (TernaryFourBlockParityGeneration.dihedral_generated LinearMap.id (fun _ _ ↦ rfl)) row125_binding

theorem row125ToTop_surjective : Function.Surjective row125ToTop :=
  GeneratedLiteralImage.toTop_surjective row125Map
    (dihedralGenerators LinearMap.id (fun _ _ ↦ rfl)) row125Generators (Equiv.swap 1 2)
    (TernaryFourBlockParityGeneration.dihedral_generated LinearMap.id (fun _ _ ↦ rfl)) row125_binding

def row79TopSocle : row79Interface.normalRegistry.QuotientSocleGeneratorFamily 2 :=
  .ofQuotientBounds _ (fun N ↦ by
    letI := N.2
    exact cyclic_socle_of_surjective ((QuotientGroup.mk' N.1).comp row79ToTop)
      ((QuotientGroup.mk'_surjective N.1).comp row79ToTop_surjective))

def row81TopSocle : row81Interface.normalRegistry.QuotientSocleGeneratorFamily 3 :=
  .ofQuotientBounds _ (fun N ↦ by
    letI := N.2
    exact dihedral_socle_of_surjective sumProjection (sumProjection_equivariant dihedralLabels)
      ((QuotientGroup.mk' N.1).comp row81ToTop)
      ((QuotientGroup.mk'_surjective N.1).comp row81ToTop_surjective))

def row125TopSocle : row125Interface.normalRegistry.QuotientSocleGeneratorFamily 3 :=
  .ofQuotientBounds _ (fun N ↦ by
    letI := N.2
    exact dihedral_socle_of_surjective LinearMap.id (fun _ _ ↦ rfl)
      ((QuotientGroup.mk' N.1).comp row125ToTop)
      ((QuotientGroup.mk'_surjective N.1).comp row125ToTop_surjective))

end PrimitiveAffineDegreeTwoTwelveParitySignImages
end SymmetricSubgroupAsymptotics

end
