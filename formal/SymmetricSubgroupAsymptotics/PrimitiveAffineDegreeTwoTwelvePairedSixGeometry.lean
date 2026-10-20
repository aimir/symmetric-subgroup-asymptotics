import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairTopLiteralTower
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelvePairedSixNaturalModules
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairTowerCyclicCapacity
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelvePairFiniteCatalogueRows151To200
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelvePairFiniteCatalogueRows201To250
import SymmetricSubgroupAsymptotics.BinaryPairFrameGenerators

/-!
# Literal twelve-to-six pair frames for exceptional rows 195 and 236

Both original twelve-point tops preserve the same displayed six pairs.
The first generator acts trivially on them and the other three induce
exactly the retained six-point generators. This supplies the actual
two-frame realization for every original pair lift, and hence its
three-position direct-kernel capacity bound.
-/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer
namespace DegreeTwoTwelvePairedSixGeometry

open DegreeTwoTwelvePairFiniteCatalogue

private def relabel : Equiv.Perm (Fin 12) where
  toFun := ![0, 11, 3, 4, 5, 6, 7, 8, 9, 10, 1, 2]
  invFun := ![0, 10, 11, 2, 3, 4, 5, 6, 7, 8, 9, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pointFrame : Fin 6 × ZMod 2 ≃ Fin 12 :=
  ((Equiv.prodCongr (Equiv.refl (Fin 6))
    (ZMod.finEquiv 2).symm.toEquiv).trans finProdFinEquiv).trans relabel

private theorem closure_range_cons_one {G : Type} [Group G]
    {n : ℕ} (g : Fin n → G) :
    Subgroup.closure (Set.range (Fin.cases 1 g)) = Subgroup.closure (Set.range g) := by
  apply le_antisymm
  · apply (Subgroup.closure_le (Subgroup.closure (Set.range g))).mpr
    rintro _ ⟨i, rfl⟩
    refine Fin.cases ?_ (fun j ↦ ?_) i
    · exact Subgroup.one_mem _
    · exact Subgroup.subset_closure ⟨j, rfl⟩
  · apply (Subgroup.closure_le (Subgroup.closure (Set.range (Fin.cases 1 g)))).mpr
    rintro _ ⟨i, rfl⟩
    exact Subgroup.subset_closure ⟨i.succ, rfl⟩

def firstTopGenerators : Fin 4 → Equiv.Perm (Fin 6) := Fin.cases 1 pairedSix1Generators
def secondTopGenerators : Fin 4 → Equiv.Perm (Fin 6) := Fin.cases 1 pairedSix2Generators

theorem first_preserves : ∀ i,
    BinaryPairFrame.Preserves pointFrame (row195Generators i) (firstTopGenerators i) := by
  unfold BinaryPairFrame.Preserves
  decide +kernel

theorem second_preserves : ∀ i,
    BinaryPairFrame.Preserves pointFrame (row236Generators i) (secondTopGenerators i) := by
  unfold BinaryPairFrame.Preserves
  decide +kernel

def row195 : DegreeTwoPairTopLiteralTower row195Interface pairedSix1Interface where
  frame := BinaryPairFrame.ofGenerators pointFrame row195Generators firstTopGenerators first_preserves
  range_eq := (BinaryPairFrame.ofGenerators_top_range
    pointFrame row195Generators firstTopGenerators first_preserves).trans
      (closure_range_cons_one pairedSix1Generators)

def row236 : DegreeTwoPairTopLiteralTower row236Interface pairedSix2Interface where
  frame := BinaryPairFrame.ofGenerators pointFrame row236Generators secondTopGenerators second_preserves
  range_eq := (BinaryPairFrame.ofGenerators_top_range
    pointFrame row236Generators secondTopGenerators second_preserves).trans
      (closure_range_cons_one pairedSix2Generators)

theorem row195_omegaSocle_capacity_le_three
    {p : PreE7PairActionClass 12} (R : DegreeTwoPairTopRealization row195Interface p)
    (N : {N : Subgroup (preE7PairAction 12 p) // N.Normal}) :
    representationSchurCapacity
      (finiteRepresentationSocle (binaryKernelOmegaConjugationRepresentation
        ((row195.realization R).rawQuotientMap N))).toRepresentation ≤ 3 :=
  DegreeTwoPairTowerCyclicCapacity.omegaSocle_capacity_le_three
    (DegreeTwoTwelvePairedSixNaturalModules.first_uniform (ZMod 2)) (row195.realization R) N

theorem row236_omegaSocle_capacity_le_three
    {p : PreE7PairActionClass 12} (R : DegreeTwoPairTopRealization row236Interface p)
    (N : {N : Subgroup (preE7PairAction 12 p) // N.Normal}) :
    representationSchurCapacity
      (finiteRepresentationSocle (binaryKernelOmegaConjugationRepresentation
        ((row236.realization R).rawQuotientMap N))).toRepresentation ≤ 3 :=
  DegreeTwoPairTowerCyclicCapacity.omegaSocle_capacity_le_three
    (DegreeTwoTwelvePairedSixNaturalModules.second_uniform (ZMod 2)) (row236.realization R) N

end DegreeTwoTwelvePairedSixGeometry
end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
