import SymmetricSubgroupAsymptotics.NestedPairOriginalNaturalSocles
import SymmetricSubgroupAsymptotics.SecondPairChartSocles
import SymmetricSubgroupAsymptotics.FiniteNormalRegistrySocleOfQuotientBounds
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveFullKernelCyclicPairNaturalFamily
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveOddPairCycleWordNaturalFamily
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveQuartetWordNaturalFamily
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveRootInheritanceNaturalFamily
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveSymmetricPairNaturalFamily

/-! Nine original joint actions use the actual nested physical pair kernel.
The all-normal bound two on their actual six-point images combines with
existing original natural capacity one. Each original normal quotient is
retained. No six-cycle or abstract group classification is required. -/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveNestedOriginalNaturalSocles

open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
open DegreeTwoTwelvePairFiniteCatalogue

def oppositeFrame : Fin 3 × ZMod 2 ≃ Fin 6 where
  toFun p := if p.2 = 0 then ![0,1,2] p.1 else ![3,4,5] p.1
  invFun x := (![0,1,2,0,1,2] x, ![0,0,0,1,1,1] x)
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row30Tops (i : Fin 3) : Equiv.Perm (Fin 6) where
  toFun := (![![0, 1, 2, 3, 4, 5], ![3, 2, 5, 4, 0, 1], ![2, 3, 0, 1, 5, 4]] : Fin 3 → Fin 6 → Fin 6) i
  invFun := (![![0, 1, 2, 3, 4, 5], ![4, 5, 1, 0, 3, 2], ![2, 3, 0, 1, 5, 4]] : Fin 3 → Fin 6 → Fin 6) i
  left_inv := by revert i; decide +kernel
  right_inv := by revert i; decide +kernel

def row30Blocks (i : Fin 3) : Equiv.Perm (Fin 3) where
  toFun := (![![0, 1, 2], ![1, 2, 0], ![1, 0, 2]] : Fin 3 → Fin 3 → Fin 3) i
  invFun := (![![0, 1, 2], ![2, 0, 1], ![1, 0, 2]] : Fin 3 → Fin 3 → Fin 3) i
  left_inv := by revert i; decide +kernel
  right_inv := by revert i; decide +kernel

theorem row30_outer_preserves : ∀ i,
    BinaryPairFrame.Preserves SecondPairChartSocles.outerFrame (row30Generators i) (row30Tops i) := by
  unfold BinaryPairFrame.Preserves
  decide +kernel

theorem row30_inner_preserves : ∀ i,
    BinaryPairFrame.Preserves SecondPairChartSocles.innerFrame (row30Tops i) (row30Blocks i) := by
  unfold BinaryPairFrame.Preserves
  decide +kernel

theorem row30AtThree_quotientSocle (N : Subgroup Row30Top) [N.Normal] :
    SocleNormalGeneratorBound (Row30Top ⧸ N) 3 := by
  exact NestedPairOriginalNaturalSocles.quotientSocle_of_generators
    SecondPairChartSocles.outerFrame SecondPairChartSocles.innerFrame row30Generators row30Tops row30Blocks
    row30_outer_preserves row30_inner_preserves 1 (by decide +kernel)
    SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveRootInheritanceNaturalFamily.row30Natural N

def row30AtThree_family : row30Interface.normalRegistry.QuotientSocleGeneratorFamily 3 :=
  .ofQuotientBounds _ (fun N => by letI := N.2; exact row30AtThree_quotientSocle N.1)

def row50Tops (i : Fin 4) : Equiv.Perm (Fin 6) where
  toFun := (![![0, 1, 2, 3, 4, 5], ![0, 1, 2, 3, 4, 5], ![3, 2, 5, 4, 0, 1], ![2, 3, 0, 1, 5, 4]] : Fin 4 → Fin 6 → Fin 6) i
  invFun := (![![0, 1, 2, 3, 4, 5], ![0, 1, 2, 3, 4, 5], ![4, 5, 1, 0, 3, 2], ![2, 3, 0, 1, 5, 4]] : Fin 4 → Fin 6 → Fin 6) i
  left_inv := by revert i; decide +kernel
  right_inv := by revert i; decide +kernel

def row50Blocks (i : Fin 4) : Equiv.Perm (Fin 3) where
  toFun := (![![0, 1, 2], ![0, 1, 2], ![1, 2, 0], ![1, 0, 2]] : Fin 4 → Fin 3 → Fin 3) i
  invFun := (![![0, 1, 2], ![0, 1, 2], ![2, 0, 1], ![1, 0, 2]] : Fin 4 → Fin 3 → Fin 3) i
  left_inv := by revert i; decide +kernel
  right_inv := by revert i; decide +kernel

theorem row50_outer_preserves : ∀ i,
    BinaryPairFrame.Preserves SecondPairChartSocles.outerFrame (row50Generators i) (row50Tops i) := by
  unfold BinaryPairFrame.Preserves
  decide +kernel

theorem row50_inner_preserves : ∀ i,
    BinaryPairFrame.Preserves SecondPairChartSocles.innerFrame (row50Tops i) (row50Blocks i) := by
  unfold BinaryPairFrame.Preserves
  decide +kernel

theorem row50AtThree_quotientSocle (N : Subgroup Row50Top) [N.Normal] :
    SocleNormalGeneratorBound (Row50Top ⧸ N) 3 := by
  exact NestedPairOriginalNaturalSocles.quotientSocle_of_generators
    SecondPairChartSocles.outerFrame SecondPairChartSocles.innerFrame row50Generators row50Tops row50Blocks
    row50_outer_preserves row50_inner_preserves 2 (by decide +kernel)
    SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveQuartetWordNaturalFamily.row50Natural N

def row50AtThree_family : row50Interface.normalRegistry.QuotientSocleGeneratorFamily 3 :=
  .ofQuotientBounds _ (fun N => by letI := N.2; exact row50AtThree_quotientSocle N.1)

def row98Tops (i : Fin 4) : Equiv.Perm (Fin 6) where
  toFun := (![![0, 1, 2, 3, 4, 5], ![1, 0, 2, 3, 5, 4], ![3, 2, 5, 4, 0, 1], ![2, 3, 0, 1, 5, 4]] : Fin 4 → Fin 6 → Fin 6) i
  invFun := (![![0, 1, 2, 3, 4, 5], ![1, 0, 2, 3, 5, 4], ![4, 5, 1, 0, 3, 2], ![2, 3, 0, 1, 5, 4]] : Fin 4 → Fin 6 → Fin 6) i
  left_inv := by revert i; decide +kernel
  right_inv := by revert i; decide +kernel

def row98Blocks (i : Fin 4) : Equiv.Perm (Fin 3) where
  toFun := (![![0, 1, 2], ![0, 1, 2], ![1, 2, 0], ![1, 0, 2]] : Fin 4 → Fin 3 → Fin 3) i
  invFun := (![![0, 1, 2], ![0, 1, 2], ![2, 0, 1], ![1, 0, 2]] : Fin 4 → Fin 3 → Fin 3) i
  left_inv := by revert i; decide +kernel
  right_inv := by revert i; decide +kernel

theorem row98_outer_preserves : ∀ i,
    BinaryPairFrame.Preserves SecondPairChartSocles.outerFrame (row98Generators i) (row98Tops i) := by
  unfold BinaryPairFrame.Preserves
  decide +kernel

theorem row98_inner_preserves : ∀ i,
    BinaryPairFrame.Preserves SecondPairChartSocles.innerFrame (row98Tops i) (row98Blocks i) := by
  unfold BinaryPairFrame.Preserves
  decide +kernel

theorem row98AtThree_quotientSocle (N : Subgroup Row98Top) [N.Normal] :
    SocleNormalGeneratorBound (Row98Top ⧸ N) 3 := by
  exact NestedPairOriginalNaturalSocles.quotientSocle_of_generators
    SecondPairChartSocles.outerFrame SecondPairChartSocles.innerFrame row98Generators row98Tops row98Blocks
    row98_outer_preserves row98_inner_preserves 2 (by decide +kernel)
    SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveRootInheritanceNaturalFamily.row98Natural N

def row98AtThree_family : row98Interface.normalRegistry.QuotientSocleGeneratorFamily 3 :=
  .ofQuotientBounds _ (fun N => by letI := N.2; exact row98AtThree_quotientSocle N.1)

def row99Tops (i : Fin 4) : Equiv.Perm (Fin 6) where
  toFun := (![![0, 1, 2, 3, 4, 5], ![2, 3, 4, 5, 0, 1], ![0, 1, 3, 2, 5, 4], ![0, 1, 2, 3, 5, 4]] : Fin 4 → Fin 6 → Fin 6) i
  invFun := (![![0, 1, 2, 3, 4, 5], ![4, 5, 0, 1, 2, 3], ![0, 1, 3, 2, 5, 4], ![0, 1, 2, 3, 5, 4]] : Fin 4 → Fin 6 → Fin 6) i
  left_inv := by revert i; decide +kernel
  right_inv := by revert i; decide +kernel

def row99Blocks (i : Fin 4) : Equiv.Perm (Fin 3) where
  toFun := (![![0, 1, 2], ![1, 2, 0], ![0, 1, 2], ![0, 1, 2]] : Fin 4 → Fin 3 → Fin 3) i
  invFun := (![![0, 1, 2], ![2, 0, 1], ![0, 1, 2], ![0, 1, 2]] : Fin 4 → Fin 3 → Fin 3) i
  left_inv := by revert i; decide +kernel
  right_inv := by revert i; decide +kernel

theorem row99_outer_preserves : ∀ i,
    BinaryPairFrame.Preserves SixPairCyclicSymmetricSocles.pointChart (row99Generators i) (row99Tops i) := by
  unfold BinaryPairFrame.Preserves
  decide +kernel

theorem row99_inner_preserves : ∀ i,
    BinaryPairFrame.Preserves SecondPairChartSocles.innerFrame (row99Tops i) (row99Blocks i) := by
  unfold BinaryPairFrame.Preserves
  decide +kernel

theorem row99AtThree_quotientSocle (N : Subgroup Row99Top) [N.Normal] :
    SocleNormalGeneratorBound (Row99Top ⧸ N) 3 := by
  exact NestedPairOriginalNaturalSocles.quotientSocle_of_generators
    SixPairCyclicSymmetricSocles.pointChart SecondPairChartSocles.innerFrame row99Generators row99Tops row99Blocks
    row99_outer_preserves row99_inner_preserves 1 (by decide +kernel)
    SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveOddPairCycleWordNaturalFamily.row99Natural N

def row99AtThree_family : row99Interface.normalRegistry.QuotientSocleGeneratorFamily 3 :=
  .ofQuotientBounds _ (fun N => by letI := N.2; exact row99AtThree_quotientSocle N.1)

def row104Tops (i : Fin 3) : Equiv.Perm (Fin 6) where
  toFun := (![![0, 1, 2, 3, 4, 5], ![2, 3, 4, 5, 0, 1], ![0, 1, 2, 3, 5, 4]] : Fin 3 → Fin 6 → Fin 6) i
  invFun := (![![0, 1, 2, 3, 4, 5], ![4, 5, 0, 1, 2, 3], ![0, 1, 2, 3, 5, 4]] : Fin 3 → Fin 6 → Fin 6) i
  left_inv := by revert i; decide +kernel
  right_inv := by revert i; decide +kernel

def row104Blocks (i : Fin 3) : Equiv.Perm (Fin 3) where
  toFun := (![![0, 1, 2], ![1, 2, 0], ![0, 1, 2]] : Fin 3 → Fin 3 → Fin 3) i
  invFun := (![![0, 1, 2], ![2, 0, 1], ![0, 1, 2]] : Fin 3 → Fin 3 → Fin 3) i
  left_inv := by revert i; decide +kernel
  right_inv := by revert i; decide +kernel

theorem row104_outer_preserves : ∀ i,
    BinaryPairFrame.Preserves SixPairCyclicSymmetricSocles.pointChart (row104Generators i) (row104Tops i) := by
  unfold BinaryPairFrame.Preserves
  decide +kernel

theorem row104_inner_preserves : ∀ i,
    BinaryPairFrame.Preserves SecondPairChartSocles.innerFrame (row104Tops i) (row104Blocks i) := by
  unfold BinaryPairFrame.Preserves
  decide +kernel

theorem row104AtThree_quotientSocle (N : Subgroup Row104Top) [N.Normal] :
    SocleNormalGeneratorBound (Row104Top ⧸ N) 3 := by
  exact NestedPairOriginalNaturalSocles.quotientSocle_of_generators
    SixPairCyclicSymmetricSocles.pointChart SecondPairChartSocles.innerFrame row104Generators row104Tops row104Blocks
    row104_outer_preserves row104_inner_preserves 1 (by decide +kernel)
    SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveOddPairCycleWordNaturalFamily.row104Natural N

def row104AtThree_family : row104Interface.normalRegistry.QuotientSocleGeneratorFamily 3 :=
  .ofQuotientBounds _ (fun N => by letI := N.2; exact row104AtThree_quotientSocle N.1)

def row152Tops (i : Fin 4) : Equiv.Perm (Fin 6) where
  toFun := (![![0, 1, 2, 3, 4, 5], ![2, 3, 4, 5, 0, 1], ![0, 1, 4, 5, 3, 2], ![0, 1, 4, 5, 2, 3]] : Fin 4 → Fin 6 → Fin 6) i
  invFun := (![![0, 1, 2, 3, 4, 5], ![4, 5, 0, 1, 2, 3], ![0, 1, 5, 4, 2, 3], ![0, 1, 4, 5, 2, 3]] : Fin 4 → Fin 6 → Fin 6) i
  left_inv := by revert i; decide +kernel
  right_inv := by revert i; decide +kernel

def row152Blocks (i : Fin 4) : Equiv.Perm (Fin 3) where
  toFun := (![![0, 1, 2], ![1, 2, 0], ![0, 2, 1], ![0, 2, 1]] : Fin 4 → Fin 3 → Fin 3) i
  invFun := (![![0, 1, 2], ![2, 0, 1], ![0, 2, 1], ![0, 2, 1]] : Fin 4 → Fin 3 → Fin 3) i
  left_inv := by revert i; decide +kernel
  right_inv := by revert i; decide +kernel

theorem row152_outer_preserves : ∀ i,
    BinaryPairFrame.Preserves SixPairCyclicSymmetricSocles.pointChart (row152Generators i) (row152Tops i) := by
  unfold BinaryPairFrame.Preserves
  decide +kernel

theorem row152_inner_preserves : ∀ i,
    BinaryPairFrame.Preserves SecondPairChartSocles.innerFrame (row152Tops i) (row152Blocks i) := by
  unfold BinaryPairFrame.Preserves
  decide +kernel

theorem row152AtThree_quotientSocle (N : Subgroup Row152Top) [N.Normal] :
    SocleNormalGeneratorBound (Row152Top ⧸ N) 3 := by
  exact NestedPairOriginalNaturalSocles.quotientSocle_of_generators
    SixPairCyclicSymmetricSocles.pointChart SecondPairChartSocles.innerFrame row152Generators row152Tops row152Blocks
    row152_outer_preserves row152_inner_preserves 1 (by decide +kernel)
    SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveOddPairCycleWordNaturalFamily.row152Natural N

def row152AtThree_family : row152Interface.normalRegistry.QuotientSocleGeneratorFamily 3 :=
  .ofQuotientBounds _ (fun N => by letI := N.2; exact row152AtThree_quotientSocle N.1)

def row153Tops (i : Fin 4) : Equiv.Perm (Fin 6) where
  toFun := (![![0, 1, 2, 3, 4, 5], ![2, 3, 4, 5, 0, 1], ![1, 0, 4, 5, 3, 2], ![1, 0, 3, 2, 5, 4]] : Fin 4 → Fin 6 → Fin 6) i
  invFun := (![![0, 1, 2, 3, 4, 5], ![4, 5, 0, 1, 2, 3], ![1, 0, 5, 4, 2, 3], ![1, 0, 3, 2, 5, 4]] : Fin 4 → Fin 6 → Fin 6) i
  left_inv := by revert i; decide +kernel
  right_inv := by revert i; decide +kernel

def row153Blocks (i : Fin 4) : Equiv.Perm (Fin 3) where
  toFun := (![![0, 1, 2], ![1, 2, 0], ![0, 2, 1], ![0, 1, 2]] : Fin 4 → Fin 3 → Fin 3) i
  invFun := (![![0, 1, 2], ![2, 0, 1], ![0, 2, 1], ![0, 1, 2]] : Fin 4 → Fin 3 → Fin 3) i
  left_inv := by revert i; decide +kernel
  right_inv := by revert i; decide +kernel

theorem row153_outer_preserves : ∀ i,
    BinaryPairFrame.Preserves SixPairCyclicSymmetricSocles.pointChart (row153Generators i) (row153Tops i) := by
  unfold BinaryPairFrame.Preserves
  decide +kernel

theorem row153_inner_preserves : ∀ i,
    BinaryPairFrame.Preserves SecondPairChartSocles.innerFrame (row153Tops i) (row153Blocks i) := by
  unfold BinaryPairFrame.Preserves
  decide +kernel

theorem row153AtThree_quotientSocle (N : Subgroup Row153Top) [N.Normal] :
    SocleNormalGeneratorBound (Row153Top ⧸ N) 3 := by
  exact NestedPairOriginalNaturalSocles.quotientSocle_of_generators
    SixPairCyclicSymmetricSocles.pointChart SecondPairChartSocles.innerFrame row153Generators row153Tops row153Blocks
    row153_outer_preserves row153_inner_preserves 1 (by decide +kernel)
    SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveOddPairCycleWordNaturalFamily.row153Natural N

def row153AtThree_family : row153Interface.normalRegistry.QuotientSocleGeneratorFamily 3 :=
  .ofQuotientBounds _ (fun N => by letI := N.2; exact row153AtThree_quotientSocle N.1)

def row192Tops (i : Fin 4) : Equiv.Perm (Fin 6) where
  toFun := (![![0, 1, 2, 3, 4, 5], ![0, 4, 5, 3, 1, 2], ![2, 3, 4, 5, 0, 1], ![3, 5, 4, 0, 2, 1]] : Fin 4 → Fin 6 → Fin 6) i
  invFun := (![![0, 1, 2, 3, 4, 5], ![0, 4, 5, 3, 1, 2], ![4, 5, 0, 1, 2, 3], ![3, 5, 4, 0, 2, 1]] : Fin 4 → Fin 6 → Fin 6) i
  left_inv := by revert i; decide +kernel
  right_inv := by revert i; decide +kernel

def row192Blocks (i : Fin 4) : Equiv.Perm (Fin 3) where
  toFun := (![![0, 1, 2], ![0, 1, 2], ![2, 0, 1], ![0, 2, 1]] : Fin 4 → Fin 3 → Fin 3) i
  invFun := (![![0, 1, 2], ![0, 1, 2], ![1, 2, 0], ![0, 2, 1]] : Fin 4 → Fin 3 → Fin 3) i
  left_inv := by revert i; decide +kernel
  right_inv := by revert i; decide +kernel

theorem row192_outer_preserves : ∀ i,
    BinaryPairFrame.Preserves SixPairCyclicSymmetricSocles.pointChart (row192Generators i) (row192Tops i) := by
  unfold BinaryPairFrame.Preserves
  decide +kernel

theorem row192_inner_preserves : ∀ i,
    BinaryPairFrame.Preserves oppositeFrame (row192Tops i) (row192Blocks i) := by
  unfold BinaryPairFrame.Preserves
  decide +kernel

theorem row192AtThree_quotientSocle (N : Subgroup Row192Top) [N.Normal] :
    SocleNormalGeneratorBound (Row192Top ⧸ N) 3 := by
  let F := BinaryPairFrame.ofGenerators SixPairCyclicSymmetricSocles.pointChart
    row192Generators row192Tops row192_outer_preserves
  let E := BinaryPairFrame.ofGenerators oppositeFrame
    row192Tops row192Blocks row192_inner_preserves
  have hr : E.top (closureGenerators row192Tops 2) = row192Blocks 2 :=
    BinaryPairFrame.ofGenerators_top_generator _ _ _ row192_inner_preserves 2
  apply ThreePairNormalGenerators.quotientSocle_of_original_natural E F
    (BinaryPairFrame.ofGenerators_top_range _ _ _ row192_outer_preserves)
    (closureGenerators row192Tops 2)⁻¹ ?_ SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveSymmetricPairNaturalFamily.row192Natural N
  simp only [map_inv,hr]
  decide +kernel

def row192AtThree_family : row192Interface.normalRegistry.QuotientSocleGeneratorFamily 3 :=
  .ofQuotientBounds _ (fun N => by letI := N.2; exact row192AtThree_quotientSocle N.1)

def row224Tops (i : Fin 4) : Equiv.Perm (Fin 6) where
  toFun := (![![0, 1, 2, 3, 4, 5], ![0, 4, 5, 3, 1, 2], ![2, 3, 4, 5, 0, 1], ![3, 5, 4, 0, 2, 1]] : Fin 4 → Fin 6 → Fin 6) i
  invFun := (![![0, 1, 2, 3, 4, 5], ![0, 4, 5, 3, 1, 2], ![4, 5, 0, 1, 2, 3], ![3, 5, 4, 0, 2, 1]] : Fin 4 → Fin 6 → Fin 6) i
  left_inv := by revert i; decide +kernel
  right_inv := by revert i; decide +kernel

def row224Blocks (i : Fin 4) : Equiv.Perm (Fin 3) where
  toFun := (![![0, 1, 2], ![0, 1, 2], ![2, 0, 1], ![0, 2, 1]] : Fin 4 → Fin 3 → Fin 3) i
  invFun := (![![0, 1, 2], ![0, 1, 2], ![1, 2, 0], ![0, 2, 1]] : Fin 4 → Fin 3 → Fin 3) i
  left_inv := by revert i; decide +kernel
  right_inv := by revert i; decide +kernel

theorem row224_outer_preserves : ∀ i,
    BinaryPairFrame.Preserves SixPairCyclicSymmetricSocles.pointChart (row224Generators i) (row224Tops i) := by
  unfold BinaryPairFrame.Preserves
  decide +kernel

theorem row224_inner_preserves : ∀ i,
    BinaryPairFrame.Preserves oppositeFrame (row224Tops i) (row224Blocks i) := by
  unfold BinaryPairFrame.Preserves
  decide +kernel

theorem row224AtThree_quotientSocle (N : Subgroup Row224Top) [N.Normal] :
    SocleNormalGeneratorBound (Row224Top ⧸ N) 3 := by
  let F := BinaryPairFrame.ofGenerators SixPairCyclicSymmetricSocles.pointChart
    row224Generators row224Tops row224_outer_preserves
  let E := BinaryPairFrame.ofGenerators oppositeFrame
    row224Tops row224Blocks row224_inner_preserves
  have hr : E.top (closureGenerators row224Tops 2) = row224Blocks 2 :=
    BinaryPairFrame.ofGenerators_top_generator _ _ _ row224_inner_preserves 2
  apply ThreePairNormalGenerators.quotientSocle_of_original_natural E F
    (BinaryPairFrame.ofGenerators_top_range _ _ _ row224_outer_preserves)
    (closureGenerators row224Tops 2)⁻¹ ?_ SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveFullKernelCyclicPairNaturalFamily.row224Natural N
  simp only [map_inv,hr]
  decide +kernel

def row224AtThree_family : row224Interface.normalRegistry.QuotientSocleGeneratorFamily 3 :=
  .ofQuotientBounds _ (fun N => by letI := N.2; exact row224AtThree_quotientSocle N.1)

end SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveNestedOriginalNaturalSocles

end
