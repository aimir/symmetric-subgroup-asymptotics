import SymmetricSubgroupAsymptotics.QuaternaryTripleTernaryImageMaps
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelvePairFiniteCatalogueRows1To50

/-! Exact image bindings for original joint rows29,31,55. Each has
retained kappa one. All range inclusions are witnessed by original
generator words and explicit source lifts, rather than subgroup containment. -/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace PrimitiveAffineDegreeTwoTwelveQuaternaryImageSocles

open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
open DegreeTwoTwelvePairFiniteCatalogue QuaternaryTripleTernaryWreathModel
open QuaternaryTripleTernaryImageMaps SemidirectProduct

def row29Lifts : Fin 3 → Model :=
  ![inl (Multiplicative.ofAdd (vector 1 1 2)),
    inl (Multiplicative.ofAdd (vector 1 1 1)), inr (Multiplicative.ofAdd 1)]

theorem row29_lifts (i : Fin 3) : literalMap 1 2 (row29Lifts i) = row29Generators i := by
  apply Equiv.ext
  intro x
  revert i x
  decide +kernel

theorem row29_image_zero : literalMap 1 2 (modelGenerators 0) =
    row29Generators 1 ^ 3 *
      (row29Generators 2 * row29Generators 0 * (row29Generators 2)⁻¹) := by
  apply Equiv.ext
  intro x
  revert x
  decide +kernel

theorem row29_image_one : literalMap 1 2 (modelGenerators 1) = row29Generators 2 := by
  apply Equiv.ext
  intro x
  revert x
  decide +kernel

theorem row29_images (i : Fin 2) : literalMap 1 2 (modelGenerators i) ∈ Row29Top := by
  have hg (j : Fin 3) : row29Generators j ∈ Row29Top :=
    Subgroup.subset_closure (Set.mem_range_self j)
  fin_cases i
  · change literalMap 1 2 (modelGenerators 0) ∈ Row29Top
    rw [row29_image_zero]
    exact Row29Top.mul_mem (Row29Top.pow_mem (hg 1) 3)
      (Row29Top.mul_mem (Row29Top.mul_mem (hg 2) (hg 0)) (Row29Top.inv_mem (hg 2)))
  · change literalMap 1 2 (modelGenerators 1) ∈ Row29Top
    rw [row29_image_one]
    exact hg 2

theorem row29_range : (literalMap 1 2).range = Row29Top :=
  literalMap_range 1 2 row29Generators row29Lifts row29_lifts row29_images

theorem row29_socle_of_surjective {Q : Type} [Group Q] (pi : Row29Top →* Q)
    (hpi : Function.Surjective pi) : SocleNormalGeneratorBound Q 1 :=
  QuaternaryTripleTernaryImageMaps.socle_of_surjective
    1 2 row29Generators row29Lifts row29_lifts row29_images pi hpi

theorem row29_quotientSocle (N : Subgroup Row29Top) [N.Normal] :
    SocleNormalGeneratorBound (Row29Top ⧸ N) 1 :=
  row29_socle_of_surjective (QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N)

def row29TopSocle : row29Interface.normalRegistry.QuotientSocleGeneratorFamily 1 :=
  .ofQuotientBounds _ (fun N => by letI := N.2; exact row29_quotientSocle N.1)

def row31Lifts : Fin 2 → Model :=
  ![inl (Multiplicative.ofAdd (vector 1 3 0)), inr (Multiplicative.ofAdd 1)]

theorem row31_lifts (i : Fin 2) : literalMap 0 1 (row31Lifts i) = row31Generators i := by
  apply Equiv.ext
  intro x
  revert i x
  decide +kernel

theorem row31_image_zero : literalMap 0 1 (modelGenerators 0) =
    row31Generators 0 ^ 2 *
      (row31Generators 1 * row31Generators 0 * (row31Generators 1)⁻¹) ^ 3 := by
  apply Equiv.ext
  intro x
  revert x
  decide +kernel

theorem row31_image_one : literalMap 0 1 (modelGenerators 1) = row31Generators 1 := by
  apply Equiv.ext
  intro x
  revert x
  decide +kernel

theorem row31_images (i : Fin 2) : literalMap 0 1 (modelGenerators i) ∈ Row31Top := by
  have hg (j : Fin 2) : row31Generators j ∈ Row31Top :=
    Subgroup.subset_closure (Set.mem_range_self j)
  fin_cases i
  · change literalMap 0 1 (modelGenerators 0) ∈ Row31Top
    rw [row31_image_zero]
    exact Row31Top.mul_mem (Row31Top.pow_mem (hg 0) 2)
      (Row31Top.pow_mem
        (Row31Top.mul_mem (Row31Top.mul_mem (hg 1) (hg 0)) (Row31Top.inv_mem (hg 1))) 3)
  · change literalMap 0 1 (modelGenerators 1) ∈ Row31Top
    rw [row31_image_one]
    exact hg 1

theorem row31_range : (literalMap 0 1).range = Row31Top :=
  literalMap_range 0 1 row31Generators row31Lifts row31_lifts row31_images

theorem row31_socle_of_surjective {Q : Type} [Group Q] (pi : Row31Top →* Q)
    (hpi : Function.Surjective pi) : SocleNormalGeneratorBound Q 1 :=
  QuaternaryTripleTernaryImageMaps.socle_of_surjective
    0 1 row31Generators row31Lifts row31_lifts row31_images pi hpi

theorem row31_quotientSocle (N : Subgroup Row31Top) [N.Normal] :
    SocleNormalGeneratorBound (Row31Top ⧸ N) 1 :=
  row31_socle_of_surjective (QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N)

def row31TopSocle : row31Interface.normalRegistry.QuotientSocleGeneratorFamily 1 :=
  .ofQuotientBounds _ (fun N => by letI := N.2; exact row31_quotientSocle N.1)

def row55Lifts : Fin 3 → Model :=
  ![inl (Multiplicative.ofAdd (vector 3 1 1)),
    inl (Multiplicative.ofAdd (vector 1 3 0)), inr (Multiplicative.ofAdd 1)]

theorem row55_lifts (i : Fin 3) : literalMap 2 1 (row55Lifts i) = row55Generators i := by
  apply Equiv.ext
  intro x
  revert i x
  decide +kernel

theorem row55_image_zero : literalMap 2 1 (modelGenerators 0) =
    row55Generators 0 * row55Generators 1 ^ 2 *
      (row55Generators 2 * row55Generators 1 * (row55Generators 2)⁻¹) := by
  apply Equiv.ext
  intro x
  revert x
  decide +kernel

theorem row55_image_one : literalMap 2 1 (modelGenerators 1) = row55Generators 2 := by
  apply Equiv.ext
  intro x
  revert x
  decide +kernel

theorem row55_images (i : Fin 2) : literalMap 2 1 (modelGenerators i) ∈ Row55Top := by
  have hg (j : Fin 3) : row55Generators j ∈ Row55Top :=
    Subgroup.subset_closure (Set.mem_range_self j)
  fin_cases i
  · change literalMap 2 1 (modelGenerators 0) ∈ Row55Top
    rw [row55_image_zero]
    exact Row55Top.mul_mem (Row55Top.mul_mem (hg 0) (Row55Top.pow_mem (hg 1) 2))
      (Row55Top.mul_mem (Row55Top.mul_mem (hg 2) (hg 1)) (Row55Top.inv_mem (hg 2)))
  · change literalMap 2 1 (modelGenerators 1) ∈ Row55Top
    rw [row55_image_one]
    exact hg 2

theorem row55_range : (literalMap 2 1).range = Row55Top :=
  literalMap_range 2 1 row55Generators row55Lifts row55_lifts row55_images

theorem row55_socle_of_surjective {Q : Type} [Group Q] (pi : Row55Top →* Q)
    (hpi : Function.Surjective pi) : SocleNormalGeneratorBound Q 1 :=
  QuaternaryTripleTernaryImageMaps.socle_of_surjective
    2 1 row55Generators row55Lifts row55_lifts row55_images pi hpi

theorem row55_quotientSocle (N : Subgroup Row55Top) [N.Normal] :
    SocleNormalGeneratorBound (Row55Top ⧸ N) 1 :=
  row55_socle_of_surjective (QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N)

def row55TopSocle : row55Interface.normalRegistry.QuotientSocleGeneratorFamily 1 :=
  .ofQuotientBounds _ (fun N => by letI := N.2; exact row55_quotientSocle N.1)

end PrimitiveAffineDegreeTwoTwelveQuaternaryImageSocles
end SymmetricSubgroupAsymptotics

end
