import SymmetricSubgroupAsymptotics.GeneratorStablePartition
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightCanonicalCatalogue
import SymmetricSubgroupAsymptotics.PermutationStabilizerTransport

/-! The first seventeen fixed canonical degree-eight actions preserve
one of three displayed nontrivial partitions. The conclusions for the
original literal actions use their checked point conjugacies. No
classification or permutation-group enumeration is performed here. -/

set_option autoImplicit false
noncomputable section
open scoped Pointwise

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineEightImprimitiveFilter

open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer

def pairedLabel (x : Fin 8) : Fin 4 := ![0, 1, 2, 2, 1, 0, 3, 3] x

def halfLabel (x : Fin 8) : Fin 2 := ![0, 0, 0, 1, 1, 1, 1, 0] x

def oppositeLabel (x : Fin 8) : Fin 4 := ![0, 1, 2, 3, 0, 1, 2, 3] x

private theorem preserves1 : ∀ i x y,
    pairedLabel (PrimitiveAffineEightTop1CatalogueBinding.catalogueGenerators i x) =
      pairedLabel (PrimitiveAffineEightTop1CatalogueBinding.catalogueGenerators i y) ↔
        pairedLabel x = pairedLabel y := by
  decide +kernel

private theorem preserves2 : ∀ i x y,
    halfLabel (PrimitiveAffineEightTop2CatalogueBinding.catalogueGenerators i x) =
      halfLabel (PrimitiveAffineEightTop2CatalogueBinding.catalogueGenerators i y) ↔
        halfLabel x = halfLabel y := by
  decide +kernel

private theorem preserves3 : ∀ i x y,
    halfLabel (PrimitiveAffineEightTop3CatalogueBinding.catalogueGenerators i x) =
      halfLabel (PrimitiveAffineEightTop3CatalogueBinding.catalogueGenerators i y) ↔
        halfLabel x = halfLabel y := by
  decide +kernel

private theorem preserves4 : ∀ i x y,
    halfLabel (PrimitiveAffineEightTop4CatalogueBinding.catalogueGenerators i x) =
      halfLabel (PrimitiveAffineEightTop4CatalogueBinding.catalogueGenerators i y) ↔
        halfLabel x = halfLabel y := by
  decide +kernel

private theorem preserves5 : ∀ i x y,
    halfLabel (PrimitiveAffineEightTop5CatalogueBinding.catalogueGenerators i x) =
      halfLabel (PrimitiveAffineEightTop5CatalogueBinding.catalogueGenerators i y) ↔
        halfLabel x = halfLabel y := by
  decide +kernel

private theorem preserves6 : ∀ i x y,
    pairedLabel (PrimitiveAffineEightTop6CatalogueBinding.catalogueGenerators i x) =
      pairedLabel (PrimitiveAffineEightTop6CatalogueBinding.catalogueGenerators i y) ↔
        pairedLabel x = pairedLabel y := by
  decide +kernel

private theorem preserves7 : ∀ i x y,
    halfLabel (PrimitiveAffineEightTop7CatalogueBinding.catalogueGenerators i x) =
      halfLabel (PrimitiveAffineEightTop7CatalogueBinding.catalogueGenerators i y) ↔
        halfLabel x = halfLabel y := by
  decide +kernel

private theorem preserves8 : ∀ i x y,
    halfLabel (PrimitiveAffineEightTop8CatalogueBinding.catalogueGenerators i x) =
      halfLabel (PrimitiveAffineEightTop8CatalogueBinding.catalogueGenerators i y) ↔
        halfLabel x = halfLabel y := by
  decide +kernel

private theorem preserves9 : ∀ i x y,
    halfLabel (PrimitiveAffineEightTop9CatalogueBinding.catalogueGenerators i x) =
      halfLabel (PrimitiveAffineEightTop9CatalogueBinding.catalogueGenerators i y) ↔
        halfLabel x = halfLabel y := by
  decide +kernel

private theorem preserves10 : ∀ i x y,
    halfLabel (PrimitiveAffineEightTop10CatalogueBinding.catalogueGenerators i x) =
      halfLabel (PrimitiveAffineEightTop10CatalogueBinding.catalogueGenerators i y) ↔
        halfLabel x = halfLabel y := by
  decide +kernel

private theorem preserves11 : ∀ i x y,
    oppositeLabel (PrimitiveAffineEightTop11CatalogueBinding.catalogueGenerators i x) =
      oppositeLabel (PrimitiveAffineEightTop11CatalogueBinding.catalogueGenerators i y) ↔
        oppositeLabel x = oppositeLabel y := by
  decide +kernel

private theorem preserves12 : ∀ i x y,
    pairedLabel (PrimitiveAffineEightTop12CatalogueBinding.catalogueGenerators i x) =
      pairedLabel (PrimitiveAffineEightTop12CatalogueBinding.catalogueGenerators i y) ↔
        pairedLabel x = pairedLabel y := by
  decide +kernel

private theorem preserves13 : ∀ i x y,
    oppositeLabel (PrimitiveAffineEightTop13CatalogueBinding.catalogueGenerators i x) =
      oppositeLabel (PrimitiveAffineEightTop13CatalogueBinding.catalogueGenerators i y) ↔
        oppositeLabel x = oppositeLabel y := by
  decide +kernel

private theorem preserves14 : ∀ i x y,
    oppositeLabel (PrimitiveAffineEightTop14CatalogueBinding.catalogueGenerators i x) =
      oppositeLabel (PrimitiveAffineEightTop14CatalogueBinding.catalogueGenerators i y) ↔
        oppositeLabel x = oppositeLabel y := by
  decide +kernel

private theorem preserves15 : ∀ i x y,
    pairedLabel (PrimitiveAffineEightTop15CatalogueBinding.catalogueGenerators i x) =
      pairedLabel (PrimitiveAffineEightTop15CatalogueBinding.catalogueGenerators i y) ↔
        pairedLabel x = pairedLabel y := by
  decide +kernel

private theorem preserves16 : ∀ i x y,
    oppositeLabel (PrimitiveAffineEightTop16CatalogueBinding.catalogueGenerators i x) =
      oppositeLabel (PrimitiveAffineEightTop16CatalogueBinding.catalogueGenerators i y) ↔
        oppositeLabel x = oppositeLabel y := by
  decide +kernel

private theorem preserves17 : ∀ i x y,
    oppositeLabel (PrimitiveAffineEightTop17CatalogueBinding.catalogueGenerators i x) =
      oppositeLabel (PrimitiveAffineEightTop17CatalogueBinding.catalogueGenerators i y) ↔
        oppositeLabel x = oppositeLabel y := by
  decide +kernel

theorem canonical_not_preprimitive (j : Fin 24) (hj : j.val < 17) :
    ¬ MulAction.IsPreprimitive (DegreeEightCanonicalCatalogue.canonical j) (Fin 8) := by
  fin_cases j
  · exact GeneratorStablePartition.not_preprimitive pairedLabel
      PrimitiveAffineEightTop1CatalogueBinding.catalogueGenerators preserves1
      0 5 1 (by decide) (by decide) (by decide)
  · exact GeneratorStablePartition.not_preprimitive halfLabel
      PrimitiveAffineEightTop2CatalogueBinding.catalogueGenerators preserves2
      0 1 3 (by decide) (by decide) (by decide)
  · exact GeneratorStablePartition.not_preprimitive halfLabel
      PrimitiveAffineEightTop3CatalogueBinding.catalogueGenerators preserves3
      0 1 3 (by decide) (by decide) (by decide)
  · exact GeneratorStablePartition.not_preprimitive halfLabel
      PrimitiveAffineEightTop4CatalogueBinding.catalogueGenerators preserves4
      0 1 3 (by decide) (by decide) (by decide)
  · exact GeneratorStablePartition.not_preprimitive halfLabel
      PrimitiveAffineEightTop5CatalogueBinding.catalogueGenerators preserves5
      0 1 3 (by decide) (by decide) (by decide)
  · exact GeneratorStablePartition.not_preprimitive pairedLabel
      PrimitiveAffineEightTop6CatalogueBinding.catalogueGenerators preserves6
      0 5 1 (by decide) (by decide) (by decide)
  · exact GeneratorStablePartition.not_preprimitive halfLabel
      PrimitiveAffineEightTop7CatalogueBinding.catalogueGenerators preserves7
      0 1 3 (by decide) (by decide) (by decide)
  · exact GeneratorStablePartition.not_preprimitive halfLabel
      PrimitiveAffineEightTop8CatalogueBinding.catalogueGenerators preserves8
      0 1 3 (by decide) (by decide) (by decide)
  · exact GeneratorStablePartition.not_preprimitive halfLabel
      PrimitiveAffineEightTop9CatalogueBinding.catalogueGenerators preserves9
      0 1 3 (by decide) (by decide) (by decide)
  · exact GeneratorStablePartition.not_preprimitive halfLabel
      PrimitiveAffineEightTop10CatalogueBinding.catalogueGenerators preserves10
      0 1 3 (by decide) (by decide) (by decide)
  · exact GeneratorStablePartition.not_preprimitive oppositeLabel
      PrimitiveAffineEightTop11CatalogueBinding.catalogueGenerators preserves11
      0 4 1 (by decide) (by decide) (by decide)
  · exact GeneratorStablePartition.not_preprimitive pairedLabel
      PrimitiveAffineEightTop12CatalogueBinding.catalogueGenerators preserves12
      0 5 1 (by decide) (by decide) (by decide)
  · exact GeneratorStablePartition.not_preprimitive oppositeLabel
      PrimitiveAffineEightTop13CatalogueBinding.catalogueGenerators preserves13
      0 4 1 (by decide) (by decide) (by decide)
  · exact GeneratorStablePartition.not_preprimitive oppositeLabel
      PrimitiveAffineEightTop14CatalogueBinding.catalogueGenerators preserves14
      0 4 1 (by decide) (by decide) (by decide)
  · exact GeneratorStablePartition.not_preprimitive pairedLabel
      PrimitiveAffineEightTop15CatalogueBinding.catalogueGenerators preserves15
      0 5 1 (by decide) (by decide) (by decide)
  · exact GeneratorStablePartition.not_preprimitive oppositeLabel
      PrimitiveAffineEightTop16CatalogueBinding.catalogueGenerators preserves16
      0 4 1 (by decide) (by decide) (by decide)
  · exact GeneratorStablePartition.not_preprimitive oppositeLabel
      PrimitiveAffineEightTop17CatalogueBinding.catalogueGenerators preserves17
      0 4 1 (by decide) (by decide) (by decide)
  · change 17 < 17 at hj
    omega
  · change 18 < 17 at hj
    omega
  · change 19 < 17 at hj
    omega
  · change 20 < 17 at hj
    omega
  · change 21 < 17 at hj
    omega
  · change 22 < 17 at hj
    omega
  · change 23 < 17 at hj
    omega

theorem literal_not_preprimitive (j : Fin 24) (hj : j.val < 17) :
    ¬ MulAction.IsPreprimitive (DegreeTwoPairedEightSharedTops.interface j).top
      (Fin 8) := by
  intro hp
  letI := hp
  let S := (DegreeTwoPairedEightSharedTops.interface j).top
  let T := DegreeEightCanonicalCatalogue.canonical j
  let c := DegreeEightCanonicalCatalogue.conjugator j
  let e : S ≃* T := actionConjugacyEquiv c
    (DegreeEightCanonicalCatalogue.literal_conjugated_eq j)
  let f : MulActionHom e (Fin 8) (Fin 8) := {
    toFun := c
    map_smul' := by
      intro g x
      change c (g.1 x) = c (g.1 (c.symm (c x)))
      rw [c.symm_apply_apply] }
  exact canonical_not_preprimitive j hj
    (MulAction.IsPreprimitive.of_surjective (f := f) c.surjective)

theorem primitive_index_ge (j : Fin 24)
    [MulAction.IsPreprimitive (DegreeTwoPairedEightSharedTops.interface j).top
      (Fin 8)] : 17 ≤ j.val := by
  by_contra h
  exact literal_not_preprimitive j (by omega) inferInstance

end SymmetricSubgroupAsymptotics.PrimitiveAffineEightImprimitiveFilter

end

