import SymmetricSubgroupAsymptotics.BinaryPlaneDiagonalBlockSocles
import SymmetricSubgroupAsymptotics.FiniteNormalRegistrySocleOfQuotientBounds
import SymmetricSubgroupAsymptotics.GeneratedLiteralImage
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelvePairFiniteCatalogueRows101To150
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelvePairFiniteCatalogueRows151To200
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelvePairFiniteCatalogueRows201To250

/-! Nine exact literal clients of the common diagonal-local binary-plane model. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveDiagonalSingerSocles

open BinaryPlanePermutationAffineEquiv BinaryPlaneDiagonalBlockSocles
open LinearSemidirectSubgroupKernelChart
open Non2UnipotentPrefixFiniteMenu Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
open DegreeTwoTwelvePairFiniteCatalogue

def row127Lifts : Fin 4 → Affine :=
  ![⟨Multiplicative.ofAdd (![![1,1],![0,0],![1,1]] : Vector),(linearPart (localPerm 1),1)⟩,
  ⟨Multiplicative.ofAdd (![![0,1],![1,1],![1,0]] : Vector),(linearPart (localPerm (Equiv.swap 1 2 * Equiv.swap 1 3)),1)⟩,
  ⟨Multiplicative.ofAdd (![![0,1],![1,1],![1,0]] : Vector),(linearPart (localPerm 1),(Equiv.swap 0 2 * Equiv.swap 0 1))⟩,
  ⟨Multiplicative.ofAdd (![![0,0],![0,0],![0,0]] : Vector),(linearPart (localPerm (Equiv.swap 1 2)),(Equiv.swap 0 1))⟩]

theorem row127_bindings (i : Fin 4) :
    action (row127Lifts i) = row127Generators i := by
  apply Equiv.ext; intro x; revert i x; decide +kernel

def row128Lifts : Fin 4 → Affine :=
  ![⟨Multiplicative.ofAdd (![![1,1],![0,0],![1,1]] : Vector),(linearPart (localPerm 1),1)⟩,
  ⟨Multiplicative.ofAdd (![![0,1],![1,1],![1,0]] : Vector),(linearPart (localPerm (Equiv.swap 1 2 * Equiv.swap 1 3)),1)⟩,
  ⟨Multiplicative.ofAdd (![![0,1],![1,1],![1,0]] : Vector),(linearPart (localPerm 1),(Equiv.swap 0 2 * Equiv.swap 0 1))⟩,
  ⟨Multiplicative.ofAdd (![![1,1],![1,1],![0,0]] : Vector),(linearPart (localPerm 1),(Equiv.swap 0 1))⟩]

theorem row128_bindings (i : Fin 4) :
    action (row128Lifts i) = row128Generators i := by
  apply Equiv.ext; intro x; revert i x; decide +kernel

def row129Lifts : Fin 4 → Affine :=
  ![⟨Multiplicative.ofAdd (![![1,1],![0,0],![1,1]] : Vector),(linearPart (localPerm 1),1)⟩,
  ⟨Multiplicative.ofAdd (![![0,1],![1,1],![1,0]] : Vector),(linearPart (localPerm (Equiv.swap 1 2 * Equiv.swap 1 3)),1)⟩,
  ⟨Multiplicative.ofAdd (![![0,0],![0,0],![0,0]] : Vector),(linearPart (localPerm (Equiv.swap 1 2)),1)⟩,
  ⟨Multiplicative.ofAdd (![![0,1],![1,1],![1,0]] : Vector),(linearPart (localPerm 1),(Equiv.swap 0 2 * Equiv.swap 0 1))⟩]

theorem row129_bindings (i : Fin 4) :
    action (row129Lifts i) = row129Generators i := by
  apply Equiv.ext; intro x; revert i x; decide +kernel

def row165Lifts : Fin 5 → Affine :=
  ![⟨Multiplicative.ofAdd (![![1,1],![0,0],![1,1]] : Vector),(linearPart (localPerm 1),1)⟩,
  ⟨Multiplicative.ofAdd (![![0,1],![1,1],![1,0]] : Vector),(linearPart (localPerm (Equiv.swap 1 2 * Equiv.swap 1 3)),1)⟩,
  ⟨Multiplicative.ofAdd (![![0,0],![0,0],![0,0]] : Vector),(linearPart (localPerm (Equiv.swap 1 2)),1)⟩,
  ⟨Multiplicative.ofAdd (![![0,1],![1,1],![1,0]] : Vector),(linearPart (localPerm 1),(Equiv.swap 0 2 * Equiv.swap 0 1))⟩,
  ⟨Multiplicative.ofAdd (![![1,1],![1,1],![0,0]] : Vector),(linearPart (localPerm 1),(Equiv.swap 0 1))⟩]

theorem row165_bindings (i : Fin 5) :
    action (row165Lifts i) = row165Generators i := by
  apply Equiv.ext; intro x; revert i x; decide +kernel

def row204Lifts : Fin 5 → Affine :=
  ![⟨Multiplicative.ofAdd (![![0,0],![0,0],![1,1]] : Vector),(linearPart (localPerm 1),1)⟩,
  ⟨Multiplicative.ofAdd (![![0,0],![0,0],![0,1]] : Vector),(linearPart (localPerm 1),1)⟩,
  ⟨Multiplicative.ofAdd (![![0,0],![0,1],![1,0]] : Vector),(linearPart (localPerm (Equiv.swap 1 3 * Equiv.swap 1 2)),1)⟩,
  ⟨Multiplicative.ofAdd (![![0,1],![1,1],![1,0]] : Vector),(linearPart (localPerm 1),(Equiv.swap 0 2 * Equiv.swap 0 1))⟩,
  ⟨Multiplicative.ofAdd (![![0,0],![0,0],![0,0]] : Vector),(linearPart (localPerm (Equiv.swap 1 2)),(Equiv.swap 0 1))⟩]

theorem row204_bindings (i : Fin 5) :
    action (row204Lifts i) = row204Generators i := by
  apply Equiv.ext; intro x; revert i x; decide +kernel

def row205Lifts : Fin 5 → Affine :=
  ![⟨Multiplicative.ofAdd (![![0,0],![0,0],![1,1]] : Vector),(linearPart (localPerm 1),1)⟩,
  ⟨Multiplicative.ofAdd (![![0,0],![0,0],![0,1]] : Vector),(linearPart (localPerm 1),1)⟩,
  ⟨Multiplicative.ofAdd (![![0,0],![0,1],![1,0]] : Vector),(linearPart (localPerm (Equiv.swap 1 3 * Equiv.swap 1 2)),1)⟩,
  ⟨Multiplicative.ofAdd (![![1,1],![1,1],![0,0]] : Vector),(linearPart (localPerm (Equiv.swap 1 2)),1)⟩,
  ⟨Multiplicative.ofAdd (![![0,1],![1,1],![1,0]] : Vector),(linearPart (localPerm 1),(Equiv.swap 0 2 * Equiv.swap 0 1))⟩]

theorem row205_bindings (i : Fin 5) :
    action (row205Lifts i) = row205Generators i := by
  apply Equiv.ext; intro x; revert i x; decide +kernel

def row206Lifts : Fin 5 → Affine :=
  ![⟨Multiplicative.ofAdd (![![0,0],![0,0],![1,1]] : Vector),(linearPart (localPerm 1),1)⟩,
  ⟨Multiplicative.ofAdd (![![0,0],![0,0],![0,1]] : Vector),(linearPart (localPerm 1),1)⟩,
  ⟨Multiplicative.ofAdd (![![0,0],![0,1],![1,0]] : Vector),(linearPart (localPerm (Equiv.swap 1 3 * Equiv.swap 1 2)),1)⟩,
  ⟨Multiplicative.ofAdd (![![0,1],![1,1],![1,0]] : Vector),(linearPart (localPerm 1),(Equiv.swap 0 2 * Equiv.swap 0 1))⟩,
  ⟨Multiplicative.ofAdd (![![1,1],![1,1],![0,0]] : Vector),(linearPart (localPerm 1),(Equiv.swap 0 1))⟩]

theorem row206_bindings (i : Fin 5) :
    action (row206Lifts i) = row206Generators i := by
  apply Equiv.ext; intro x; revert i x; decide +kernel

def row239Lifts : Fin 6 → Affine :=
  ![⟨Multiplicative.ofAdd (![![0,0],![0,0],![1,1]] : Vector),(linearPart (localPerm 1),1)⟩,
  ⟨Multiplicative.ofAdd (![![0,0],![0,0],![0,1]] : Vector),(linearPart (localPerm 1),1)⟩,
  ⟨Multiplicative.ofAdd (![![0,0],![0,1],![1,0]] : Vector),(linearPart (localPerm (Equiv.swap 1 3 * Equiv.swap 1 2)),1)⟩,
  ⟨Multiplicative.ofAdd (![![1,1],![1,1],![0,0]] : Vector),(linearPart (localPerm (Equiv.swap 1 2)),1)⟩,
  ⟨Multiplicative.ofAdd (![![0,1],![1,1],![1,0]] : Vector),(linearPart (localPerm 1),(Equiv.swap 0 2 * Equiv.swap 0 1))⟩,
  ⟨Multiplicative.ofAdd (![![1,1],![1,1],![0,0]] : Vector),(linearPart (localPerm 1),(Equiv.swap 0 1))⟩]

theorem row239_bindings (i : Fin 6) :
    action (row239Lifts i) = row239Generators i := by
  apply Equiv.ext; intro x; revert i x; decide +kernel

theorem literal_quotientSocle {n : ℕ} (lifted : Fin n → Affine)
    (target : Fin n → Equiv.Perm (Fin 12))
    (hbinding : ∀ i, action (lifted i) = target i)
    (hs : localSinger ∈ Image rho (Subgroup.closure (Set.range lifted)))
    (hr : blockRotation ∈ Image rho (Subgroup.closure (Set.range lifted)))
    (N : Subgroup (Subgroup.closure (Set.range target))) [N.Normal] :
    SocleNormalGeneratorBound (Subgroup.closure (Set.range target) ⧸ N) 3 := by
  let K := Subgroup.closure (Set.range lifted)
  have htuples : ∀ L : Subgroup K, L.Normal →
      ∃ x : Fin 3 → K, Subgroup.normalClosure (Set.range x) = L := by
    intro L hL
    letI := hL
    exact exists_normal_generating_tuple_of_normalGen_le L
      (BinaryPlaneDiagonalBlockSocles.normalGen_le K hs hr L)
  let f : K →* Equiv.Perm (Fin 12) := action.comp K.subtype
  let pi := GeneratedLiteralImage.toTop f (closureGenerators lifted) target (Equiv.refl _)
    (closureGenerators_full lifted) hbinding
  have hpi : Function.Surjective pi :=
    GeneratedLiteralImage.toTop_surjective f (closureGenerators lifted) target (Equiv.refl _)
      (closureGenerators_full lifted) hbinding
  exact normal_generating_tuples_of_surjective ((QuotientGroup.mk' N).comp pi)
    ((QuotientGroup.mk'_surjective N).comp hpi) htuples
    (finiteGroupSocle _) inferInstance

theorem row127_quotientSocle (N : Subgroup Row127Top) [N.Normal] :
    SocleNormalGeneratorBound (Row127Top ⧸ N) 3 := by
  apply literal_quotientSocle row127Lifts row127Generators row127_bindings ?_ ?_ N
  · refine ⟨(closureGenerators row127Lifts 1)^2,?_⟩
    change ((row127Lifts 1).right)^2 = localSinger
    apply Prod.ext
    · apply LinearEquiv.ext; intro v; revert v; decide +kernel
    · apply Equiv.ext; intro i; revert i; decide +kernel
  · refine ⟨closureGenerators row127Lifts 2,?_⟩
    change (row127Lifts 2).right = blockRotation
    apply Prod.ext
    · apply LinearEquiv.ext; intro v; revert v; decide +kernel
    · apply Equiv.ext; intro i; revert i; decide +kernel

def row127_family : row127Interface.normalRegistry.QuotientSocleGeneratorFamily 3 :=
  FiniteNormalStateRegistry.QuotientSocleGeneratorFamily.ofQuotientBounds
    row127Interface.normalRegistry (fun N => by letI := N.2; exact row127_quotientSocle N.1)

theorem row128_quotientSocle (N : Subgroup Row128Top) [N.Normal] :
    SocleNormalGeneratorBound (Row128Top ⧸ N) 3 := by
  apply literal_quotientSocle row128Lifts row128Generators row128_bindings ?_ ?_ N
  · refine ⟨(closureGenerators row128Lifts 1)^2,?_⟩
    change ((row128Lifts 1).right)^2 = localSinger
    apply Prod.ext
    · apply LinearEquiv.ext; intro v; revert v; decide +kernel
    · apply Equiv.ext; intro i; revert i; decide +kernel
  · refine ⟨closureGenerators row128Lifts 2,?_⟩
    change (row128Lifts 2).right = blockRotation
    apply Prod.ext
    · apply LinearEquiv.ext; intro v; revert v; decide +kernel
    · apply Equiv.ext; intro i; revert i; decide +kernel

def row128_family : row128Interface.normalRegistry.QuotientSocleGeneratorFamily 3 :=
  FiniteNormalStateRegistry.QuotientSocleGeneratorFamily.ofQuotientBounds
    row128Interface.normalRegistry (fun N => by letI := N.2; exact row128_quotientSocle N.1)

theorem row129_quotientSocle (N : Subgroup Row129Top) [N.Normal] :
    SocleNormalGeneratorBound (Row129Top ⧸ N) 3 := by
  apply literal_quotientSocle row129Lifts row129Generators row129_bindings ?_ ?_ N
  · refine ⟨(closureGenerators row129Lifts 1)^2,?_⟩
    change ((row129Lifts 1).right)^2 = localSinger
    apply Prod.ext
    · apply LinearEquiv.ext; intro v; revert v; decide +kernel
    · apply Equiv.ext; intro i; revert i; decide +kernel
  · refine ⟨closureGenerators row129Lifts 3,?_⟩
    change (row129Lifts 3).right = blockRotation
    apply Prod.ext
    · apply LinearEquiv.ext; intro v; revert v; decide +kernel
    · apply Equiv.ext; intro i; revert i; decide +kernel

def row129_family : row129Interface.normalRegistry.QuotientSocleGeneratorFamily 3 :=
  FiniteNormalStateRegistry.QuotientSocleGeneratorFamily.ofQuotientBounds
    row129Interface.normalRegistry (fun N => by letI := N.2; exact row129_quotientSocle N.1)

theorem row165_quotientSocle (N : Subgroup Row165Top) [N.Normal] :
    SocleNormalGeneratorBound (Row165Top ⧸ N) 3 := by
  apply literal_quotientSocle row165Lifts row165Generators row165_bindings ?_ ?_ N
  · refine ⟨(closureGenerators row165Lifts 1)^2,?_⟩
    change ((row165Lifts 1).right)^2 = localSinger
    apply Prod.ext
    · apply LinearEquiv.ext; intro v; revert v; decide +kernel
    · apply Equiv.ext; intro i; revert i; decide +kernel
  · refine ⟨closureGenerators row165Lifts 3,?_⟩
    change (row165Lifts 3).right = blockRotation
    apply Prod.ext
    · apply LinearEquiv.ext; intro v; revert v; decide +kernel
    · apply Equiv.ext; intro i; revert i; decide +kernel

def row165_family : row165Interface.normalRegistry.QuotientSocleGeneratorFamily 3 :=
  FiniteNormalStateRegistry.QuotientSocleGeneratorFamily.ofQuotientBounds
    row165Interface.normalRegistry (fun N => by letI := N.2; exact row165_quotientSocle N.1)

theorem row204_quotientSocle (N : Subgroup Row204Top) [N.Normal] :
    SocleNormalGeneratorBound (Row204Top ⧸ N) 3 := by
  apply literal_quotientSocle row204Lifts row204Generators row204_bindings ?_ ?_ N
  · refine ⟨(closureGenerators row204Lifts 2)^1,?_⟩
    change ((row204Lifts 2).right)^1 = localSinger
    apply Prod.ext
    · apply LinearEquiv.ext; intro v; revert v; decide +kernel
    · apply Equiv.ext; intro i; revert i; decide +kernel
  · refine ⟨closureGenerators row204Lifts 3,?_⟩
    change (row204Lifts 3).right = blockRotation
    apply Prod.ext
    · apply LinearEquiv.ext; intro v; revert v; decide +kernel
    · apply Equiv.ext; intro i; revert i; decide +kernel

def row204_family : row204Interface.normalRegistry.QuotientSocleGeneratorFamily 3 :=
  FiniteNormalStateRegistry.QuotientSocleGeneratorFamily.ofQuotientBounds
    row204Interface.normalRegistry (fun N => by letI := N.2; exact row204_quotientSocle N.1)

theorem row205_quotientSocle (N : Subgroup Row205Top) [N.Normal] :
    SocleNormalGeneratorBound (Row205Top ⧸ N) 3 := by
  apply literal_quotientSocle row205Lifts row205Generators row205_bindings ?_ ?_ N
  · refine ⟨(closureGenerators row205Lifts 2)^1,?_⟩
    change ((row205Lifts 2).right)^1 = localSinger
    apply Prod.ext
    · apply LinearEquiv.ext; intro v; revert v; decide +kernel
    · apply Equiv.ext; intro i; revert i; decide +kernel
  · refine ⟨closureGenerators row205Lifts 4,?_⟩
    change (row205Lifts 4).right = blockRotation
    apply Prod.ext
    · apply LinearEquiv.ext; intro v; revert v; decide +kernel
    · apply Equiv.ext; intro i; revert i; decide +kernel

def row205_family : row205Interface.normalRegistry.QuotientSocleGeneratorFamily 3 :=
  FiniteNormalStateRegistry.QuotientSocleGeneratorFamily.ofQuotientBounds
    row205Interface.normalRegistry (fun N => by letI := N.2; exact row205_quotientSocle N.1)

theorem row206_quotientSocle (N : Subgroup Row206Top) [N.Normal] :
    SocleNormalGeneratorBound (Row206Top ⧸ N) 3 := by
  apply literal_quotientSocle row206Lifts row206Generators row206_bindings ?_ ?_ N
  · refine ⟨(closureGenerators row206Lifts 2)^1,?_⟩
    change ((row206Lifts 2).right)^1 = localSinger
    apply Prod.ext
    · apply LinearEquiv.ext; intro v; revert v; decide +kernel
    · apply Equiv.ext; intro i; revert i; decide +kernel
  · refine ⟨closureGenerators row206Lifts 3,?_⟩
    change (row206Lifts 3).right = blockRotation
    apply Prod.ext
    · apply LinearEquiv.ext; intro v; revert v; decide +kernel
    · apply Equiv.ext; intro i; revert i; decide +kernel

def row206_family : row206Interface.normalRegistry.QuotientSocleGeneratorFamily 3 :=
  FiniteNormalStateRegistry.QuotientSocleGeneratorFamily.ofQuotientBounds
    row206Interface.normalRegistry (fun N => by letI := N.2; exact row206_quotientSocle N.1)

theorem row239_quotientSocle (N : Subgroup Row239Top) [N.Normal] :
    SocleNormalGeneratorBound (Row239Top ⧸ N) 3 := by
  apply literal_quotientSocle row239Lifts row239Generators row239_bindings ?_ ?_ N
  · refine ⟨(closureGenerators row239Lifts 2)^1,?_⟩
    change ((row239Lifts 2).right)^1 = localSinger
    apply Prod.ext
    · apply LinearEquiv.ext; intro v; revert v; decide +kernel
    · apply Equiv.ext; intro i; revert i; decide +kernel
  · refine ⟨closureGenerators row239Lifts 4,?_⟩
    change (row239Lifts 4).right = blockRotation
    apply Prod.ext
    · apply LinearEquiv.ext; intro v; revert v; decide +kernel
    · apply Equiv.ext; intro i; revert i; decide +kernel

def row239_family : row239Interface.normalRegistry.QuotientSocleGeneratorFamily 3 :=
  FiniteNormalStateRegistry.QuotientSocleGeneratorFamily.ofQuotientBounds
    row239Interface.normalRegistry (fun N => by letI := N.2; exact row239_quotientSocle N.1)

end SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveDiagonalSingerSocles

end
