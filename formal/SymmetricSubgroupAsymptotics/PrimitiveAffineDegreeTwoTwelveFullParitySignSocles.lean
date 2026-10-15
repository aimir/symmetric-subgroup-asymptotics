import SymmetricSubgroupAsymptotics.TernaryFourBlockParityGeneration
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveMetacyclicImages
import SymmetricSubgroupAsymptotics.GeneratedLiteralImage
import SymmetricSubgroupAsymptotics.FiniteNormalRegistrySocleOfQuotientBounds
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelvePairFiniteCatalogueRows201To250

/-! Full-translation consumers of the established two-sign models.
The C4 and D8 actions retain the two parity sign coordinates. The existing
coprime theorem handles their reducible ternary modules at bounds two
and three. Exact generator images give the original tops and quotients. -/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveFullParitySignSocles

open TernaryFourBlockParityModels TernaryFourBlockParityGeneration
open BinaryPermutationSemidirectNormalGenerators (cyclicLabels dihedralLabels)
open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
open DegreeTwoTwelvePairFiniteCatalogue

def cyclicLiteral : CyclicAffine →* Equiv.Perm (Fin 12) :=
  PrimitiveAffineDegreeTwoTwelveMetacyclicImages.centeredPointEquiv.symm.permCongrHom.toMonoidHom.comp
    (TernaryParitySignModel.action cyclicLabels cyclicBlockAction label cyclic_label
      LinearMap.id (fun _ _ => rfl))

def dihedralLiteral : DihedralAffine LinearMap.id (fun _ _ => rfl) →* Equiv.Perm (Fin 12) :=
  PrimitiveAffineDegreeTwoTwelveMetacyclicImages.centeredPointEquiv.symm.permCongrHom.toMonoidHom.comp
    (TernaryParitySignModel.action dihedralLabels (TernaryFourBlockMetacyclicModel.blockAction true)
      label dihedral_label LinearMap.id (fun _ _ => rfl))

theorem row211_bindings (i : Fin 3) :
    cyclicLiteral (cyclicGenerators i) = row211Generators (Equiv.swap 1 2 i) := by
  apply Equiv.ext
  intro x
  revert i x
  decide +kernel

theorem row248_bindings (i : Fin 4) :
    dihedralLiteral (dihedralGenerators LinearMap.id (fun _ _ => rfl) i) =
      row248Generators (Equiv.swap 1 2 i) := by
  apply Equiv.ext
  intro x
  revert i x
  decide +kernel

def row211Map : CyclicAffine →* Row211Top :=
  GeneratedLiteralImage.toTop cyclicLiteral cyclicGenerators row211Generators
    (Equiv.swap 1 2) TernaryFourBlockParityGeneration.cyclic_generated row211_bindings

def row248Map : DihedralAffine LinearMap.id (fun _ _ => rfl) →* Row248Top :=
  GeneratedLiteralImage.toTop dihedralLiteral (dihedralGenerators LinearMap.id (fun _ _ => rfl))
    row248Generators (Equiv.swap 1 2)
    (TernaryFourBlockParityGeneration.dihedral_generated LinearMap.id (fun _ _ => rfl)) row248_bindings

theorem row211Map_surjective : Function.Surjective row211Map :=
  GeneratedLiteralImage.toTop_surjective cyclicLiteral cyclicGenerators row211Generators
    (Equiv.swap 1 2) TernaryFourBlockParityGeneration.cyclic_generated row211_bindings

theorem row248Map_surjective : Function.Surjective row248Map :=
  GeneratedLiteralImage.toTop_surjective dihedralLiteral (dihedralGenerators LinearMap.id (fun _ _ => rfl))
    row248Generators (Equiv.swap 1 2)
    (TernaryFourBlockParityGeneration.dihedral_generated LinearMap.id (fun _ _ => rfl)) row248_bindings

theorem row211_quotientSocle (N : Subgroup Row211Top) [N.Normal] :
    SocleNormalGeneratorBound (Row211Top ⧸ N) 2 :=
  cyclic_socle_of_surjective ((QuotientGroup.mk' N).comp row211Map)
    ((QuotientGroup.mk'_surjective N).comp row211Map_surjective)

theorem row248_quotientSocle (N : Subgroup Row248Top) [N.Normal] :
    SocleNormalGeneratorBound (Row248Top ⧸ N) 3 :=
  dihedral_socle_of_surjective LinearMap.id (fun _ _ => rfl)
    ((QuotientGroup.mk' N).comp row248Map)
    ((QuotientGroup.mk'_surjective N).comp row248Map_surjective)

def row211_family : row211Interface.normalRegistry.QuotientSocleGeneratorFamily 2 :=
  Non2UnipotentPrefixFiniteMenu.FiniteNormalStateRegistry.QuotientSocleGeneratorFamily.ofQuotientBounds
    row211Interface.normalRegistry (fun N => by letI := N.2; exact row211_quotientSocle N.1)

def row248_family : row248Interface.normalRegistry.QuotientSocleGeneratorFamily 3 :=
  Non2UnipotentPrefixFiniteMenu.FiniteNormalStateRegistry.QuotientSocleGeneratorFamily.ofQuotientBounds
    row248Interface.normalRegistry (fun N => by letI := N.2; exact row248_quotientSocle N.1)

end SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveFullParitySignSocles

end
