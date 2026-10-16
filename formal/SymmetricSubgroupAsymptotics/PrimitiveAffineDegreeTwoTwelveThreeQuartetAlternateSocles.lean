import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveThreeQuartetAlternateCore

/-! Nine further original three-quartet actions use the checked common
Singer words. Together with row292 these form one ten-row family. The
bound three is an explicitly proved alternate capacity, and all quotient
maps are those of the original literal target groups. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveThreeQuartetAlternateSocles

open BinaryPlanePermutationWreathCoordinates BinaryPlaneWreathIrreducible
open Non2UnipotentPrefixFiniteMenu Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
open DegreeTwoTwelvePairFiniteCatalogue
open PrimitiveAffineDegreeTwoTwelveThreeQuartetAlternateCore

theorem cyclic_quotientSocle {n : ℕ}
    (lifted : Fin n → BinaryThreeQuartetLiteralSocles.Model (R := CyclicBlocks))
    (target : Fin n → Equiv.Perm (Fin 12))
    (hbinding : ∀ i, BinaryThreeQuartetLiteralSocles.action (lifted i) = target i)
    (hcore : coreSinger ∈ Subgroup.closure (Set.range (fun i => (lifted i).right)))
    (r : Fin n) (hr : (lifted r).right = coreRotation cyclicRotation)
    (N : Subgroup (Subgroup.closure (Set.range target))) [N.Normal] :
    SocleNormalGeneratorBound (Subgroup.closure (Set.range target) ⧸ N) 3 := by
  let C := Subgroup.closure (Set.range (fun i => (lifted i).right))
  have hg : coreRotation cyclicRotation ∈ C :=
    hr ▸ Subgroup.subset_closure (Set.mem_range_self r)
  have hlocal := local_of_words C coreSinger (coreRotation cyclicRotation)
    hcore hg cyclic_words
  have hfull := cyclic_full (fun i => (lifted i).right.right) r
    (congrArg (fun q : LinearWreath (R := CyclicBlocks) => q.right) hr)
  exact BinaryThreeQuartetLiteralSocles.quotientSocle lifted target hbinding hfull hlocal
    PrimitiveAffineDegreeTwoTwelveThreeQuartetAlternatePilot.blocks_transitive
    cyclicRotation 0 PrimitiveAffineDegreeTwoTwelveThreeQuartetAlternatePilot.blocks_cycle
    1 PrimitiveAffineDegreeTwoTwelveThreeQuartetAlternatePilot.blocks_normalGen N

theorem symmetric_quotientSocle {n : ℕ}
    (lifted : Fin n → BinaryThreeQuartetLiteralSocles.Model (R := SymmetricBlocks))
    (target : Fin n → Equiv.Perm (Fin 12))
    (hbinding : ∀ i, BinaryThreeQuartetLiteralSocles.action (lifted i) = target i)
    (hcore : coreSinger ∈ Subgroup.closure (Set.range (fun i => (lifted i).right)))
    (r s : Fin n) (hr : (lifted r).right = coreRotation symmetricRotation)
    (hs : (lifted s).right.right = symmetricReflection)
    (N : Subgroup (Subgroup.closure (Set.range target))) [N.Normal] :
    SocleNormalGeneratorBound (Subgroup.closure (Set.range target) ⧸ N) 3 := by
  let C := Subgroup.closure (Set.range (fun i => (lifted i).right))
  have hg : coreRotation symmetricRotation ∈ C :=
    hr ▸ Subgroup.subset_closure (Set.mem_range_self r)
  have hlocal := local_of_words C coreSinger (coreRotation symmetricRotation)
    hcore hg symmetric_words
  have hfull := symmetric_full (fun i => (lifted i).right.right) r s
    (congrArg (fun q : LinearWreath (R := SymmetricBlocks) => q.right) hr) hs
  exact BinaryThreeQuartetLiteralSocles.quotientSocle lifted target hbinding hfull hlocal
    symmetric_transitive symmetricRotation 0 symmetric_cycle 1 symmetric_normalGen N

def row265Lifts : Fin 3 → BinaryThreeQuartetLiteralSocles.Model (R := CyclicBlocks) :=
  fun i => coordinates (![localU,localV,rotateWreath cyclicRotation] i)
def row273Lifts : Fin 4 → BinaryThreeQuartetLiteralSocles.Model (R := CyclicBlocks) :=
  fun i => coordinates (![localU,localV,twistFull,rotateWreath cyclicRotation] i)
def row275Lifts : Fin 4 → BinaryThreeQuartetLiteralSocles.Model (R := SymmetricBlocks) :=
  fun i => coordinates (![localU,localV,rotateWreath symmetricRotation,reflectA symmetricReflection] i)
def row276Lifts : Fin 4 → BinaryThreeQuartetLiteralSocles.Model (R := SymmetricBlocks) :=
  fun i => coordinates (![localU,localV,rotateWreath symmetricRotation,reflectB symmetricReflection] i)
def row283Lifts : Fin 5 → BinaryThreeQuartetLiteralSocles.Model (R := SymmetricBlocks) :=
  fun i => coordinates (![localU,localV,twistFull,rotateWreath symmetricRotation,reflectA symmetricReflection] i)
def row284Lifts : Fin 4 → BinaryThreeQuartetLiteralSocles.Model (R := CyclicBlocks) :=
  fun i => coordinates (![localU,localV,twistPair,rotateWreath cyclicRotation] i)
def row290Lifts : Fin 5 → BinaryThreeQuartetLiteralSocles.Model (R := SymmetricBlocks) :=
  fun i => coordinates (![localU,localV,twistPair,rotateWreath symmetricRotation,reflectA symmetricReflection] i)
def row291Lifts : Fin 5 → BinaryThreeQuartetLiteralSocles.Model (R := SymmetricBlocks) :=
  fun i => coordinates (![localU,localV,twistReverse,rotateWreath symmetricRotation,reflectC symmetricReflection] i)
def row294Lifts : Fin 4 → BinaryThreeQuartetLiteralSocles.Model (R := SymmetricBlocks) :=
  fun i => coordinates (![localFour,localSwap,rotateWreath symmetricRotation,reflectA symmetricReflection] i)

theorem row265_bindings (i : Fin 3) :
    BinaryThreeQuartetLiteralSocles.action (row265Lifts i) = row265Generators i := by
  apply Equiv.ext; intro x; revert i x; decide +kernel
theorem row273_bindings (i : Fin 4) :
    BinaryThreeQuartetLiteralSocles.action (row273Lifts i) = row273Generators i := by
  apply Equiv.ext; intro x; revert i x; decide +kernel
theorem row275_bindings (i : Fin 4) :
    BinaryThreeQuartetLiteralSocles.action (row275Lifts i) = row275Generators i := by
  apply Equiv.ext; intro x; revert i x; decide +kernel
theorem row276_bindings (i : Fin 4) :
    BinaryThreeQuartetLiteralSocles.action (row276Lifts i) = row276Generators i := by
  apply Equiv.ext; intro x; revert i x; decide +kernel
theorem row283_bindings (i : Fin 5) :
    BinaryThreeQuartetLiteralSocles.action (row283Lifts i) = row283Generators i := by
  apply Equiv.ext; intro x; revert i x; decide +kernel
theorem row284_bindings (i : Fin 4) :
    BinaryThreeQuartetLiteralSocles.action (row284Lifts i) = row284Generators i := by
  apply Equiv.ext; intro x; revert i x; decide +kernel
theorem row290_bindings (i : Fin 5) :
    BinaryThreeQuartetLiteralSocles.action (row290Lifts i) = row290Generators i := by
  apply Equiv.ext; intro x; revert i x; decide +kernel
theorem row291_bindings (i : Fin 5) :
    BinaryThreeQuartetLiteralSocles.action (row291Lifts i) = row291Generators i := by
  apply Equiv.ext; intro x; revert i x; decide +kernel
theorem row294_bindings (i : Fin 4) :
    BinaryThreeQuartetLiteralSocles.action (row294Lifts i) = row294Generators i := by
  apply Equiv.ext; intro x; revert i x; decide +kernel

theorem row265AtThree_quotientSocle (N : Subgroup Row265Top) [N.Normal] :
    SocleNormalGeneratorBound (Row265Top ⧸ N) 3 := by
  apply cyclic_quotientSocle row265Lifts row265Generators row265_bindings ?_ 2 rfl N
  exact Subgroup.subset_closure (Set.mem_range_self (0 : Fin 3))
theorem row273AtThree_quotientSocle (N : Subgroup Row273Top) [N.Normal] :
    SocleNormalGeneratorBound (Row273Top ⧸ N) 3 := by
  apply cyclic_quotientSocle row273Lifts row273Generators row273_bindings ?_ 3 rfl N
  exact Subgroup.subset_closure (Set.mem_range_self (0 : Fin 4))
theorem row275AtThree_quotientSocle (N : Subgroup Row275Top) [N.Normal] :
    SocleNormalGeneratorBound (Row275Top ⧸ N) 3 := by
  apply symmetric_quotientSocle row275Lifts row275Generators row275_bindings ?_ 2 3 rfl rfl N
  exact Subgroup.subset_closure (Set.mem_range_self (0 : Fin 4))
theorem row276AtThree_quotientSocle (N : Subgroup Row276Top) [N.Normal] :
    SocleNormalGeneratorBound (Row276Top ⧸ N) 3 := by
  apply symmetric_quotientSocle row276Lifts row276Generators row276_bindings ?_ 2 3 rfl rfl N
  exact Subgroup.subset_closure (Set.mem_range_self (0 : Fin 4))
theorem row283AtThree_quotientSocle (N : Subgroup Row283Top) [N.Normal] :
    SocleNormalGeneratorBound (Row283Top ⧸ N) 3 := by
  apply symmetric_quotientSocle row283Lifts row283Generators row283_bindings ?_ 3 4 rfl rfl N
  exact Subgroup.subset_closure (Set.mem_range_self (0 : Fin 5))
theorem row284AtThree_quotientSocle (N : Subgroup Row284Top) [N.Normal] :
    SocleNormalGeneratorBound (Row284Top ⧸ N) 3 := by
  apply cyclic_quotientSocle row284Lifts row284Generators row284_bindings ?_ 3 rfl N
  exact Subgroup.subset_closure (Set.mem_range_self (0 : Fin 4))
theorem row290AtThree_quotientSocle (N : Subgroup Row290Top) [N.Normal] :
    SocleNormalGeneratorBound (Row290Top ⧸ N) 3 := by
  apply symmetric_quotientSocle row290Lifts row290Generators row290_bindings ?_ 3 4 rfl rfl N
  exact Subgroup.subset_closure (Set.mem_range_self (0 : Fin 5))
theorem row291AtThree_quotientSocle (N : Subgroup Row291Top) [N.Normal] :
    SocleNormalGeneratorBound (Row291Top ⧸ N) 3 := by
  apply symmetric_quotientSocle row291Lifts row291Generators row291_bindings ?_ 3 4 rfl rfl N
  exact Subgroup.subset_closure (Set.mem_range_self (0 : Fin 5))
theorem row294AtThree_quotientSocle (N : Subgroup Row294Top) [N.Normal] :
    SocleNormalGeneratorBound (Row294Top ⧸ N) 3 := by
  apply symmetric_quotientSocle row294Lifts row294Generators row294_bindings ?_ 2 3 rfl rfl N
  rw [← symmetric_four_swap]
  exact (Subgroup.closure (Set.range (fun i => (row294Lifts i).right))).mul_mem
    (Subgroup.subset_closure (Set.mem_range_self (0 : Fin 4)))
    (Subgroup.subset_closure (Set.mem_range_self (1 : Fin 4)))

def row265AtThree_family : row265Interface.normalRegistry.QuotientSocleGeneratorFamily 3 :=
  FiniteNormalStateRegistry.QuotientSocleGeneratorFamily.ofQuotientBounds
    row265Interface.normalRegistry (fun N => by letI := N.2; exact row265AtThree_quotientSocle N.1)
def row273AtThree_family : row273Interface.normalRegistry.QuotientSocleGeneratorFamily 3 :=
  FiniteNormalStateRegistry.QuotientSocleGeneratorFamily.ofQuotientBounds
    row273Interface.normalRegistry (fun N => by letI := N.2; exact row273AtThree_quotientSocle N.1)
def row275AtThree_family : row275Interface.normalRegistry.QuotientSocleGeneratorFamily 3 :=
  FiniteNormalStateRegistry.QuotientSocleGeneratorFamily.ofQuotientBounds
    row275Interface.normalRegistry (fun N => by letI := N.2; exact row275AtThree_quotientSocle N.1)
def row276AtThree_family : row276Interface.normalRegistry.QuotientSocleGeneratorFamily 3 :=
  FiniteNormalStateRegistry.QuotientSocleGeneratorFamily.ofQuotientBounds
    row276Interface.normalRegistry (fun N => by letI := N.2; exact row276AtThree_quotientSocle N.1)
def row283AtThree_family : row283Interface.normalRegistry.QuotientSocleGeneratorFamily 3 :=
  FiniteNormalStateRegistry.QuotientSocleGeneratorFamily.ofQuotientBounds
    row283Interface.normalRegistry (fun N => by letI := N.2; exact row283AtThree_quotientSocle N.1)
def row284AtThree_family : row284Interface.normalRegistry.QuotientSocleGeneratorFamily 3 :=
  FiniteNormalStateRegistry.QuotientSocleGeneratorFamily.ofQuotientBounds
    row284Interface.normalRegistry (fun N => by letI := N.2; exact row284AtThree_quotientSocle N.1)
def row290AtThree_family : row290Interface.normalRegistry.QuotientSocleGeneratorFamily 3 :=
  FiniteNormalStateRegistry.QuotientSocleGeneratorFamily.ofQuotientBounds
    row290Interface.normalRegistry (fun N => by letI := N.2; exact row290AtThree_quotientSocle N.1)
def row291AtThree_family : row291Interface.normalRegistry.QuotientSocleGeneratorFamily 3 :=
  FiniteNormalStateRegistry.QuotientSocleGeneratorFamily.ofQuotientBounds
    row291Interface.normalRegistry (fun N => by letI := N.2; exact row291AtThree_quotientSocle N.1)
def row294AtThree_family : row294Interface.normalRegistry.QuotientSocleGeneratorFamily 3 :=
  FiniteNormalStateRegistry.QuotientSocleGeneratorFamily.ofQuotientBounds
    row294Interface.normalRegistry (fun N => by letI := N.2; exact row294AtThree_quotientSocle N.1)

end SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveThreeQuartetAlternateSocles

end
