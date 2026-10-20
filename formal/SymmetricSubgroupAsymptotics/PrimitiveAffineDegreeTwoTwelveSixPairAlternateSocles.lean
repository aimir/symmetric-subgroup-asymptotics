import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveSixPairImageSocles

/-! Three further original joint actions have quotient-socle capacity two
by the same retained physical-pair kernel theorem. These are explicitly
alternate capacities, rather than claims of their historical capacity one. -/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveSixPairAlternateSocles

open SixPairCyclicSymmetricSocles PrimitiveAffineDegreeTwoTwelveSixPairImageSocles
open Non2UnipotentPrefixFiniteMenu
open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
open DegreeTwoTwelvePairFiniteCatalogue

def redundantCyclicTops : Fin 3 → Equiv.Perm (Fin 6) := ![1,1,cycle]

theorem row58_preserves : ∀ i,
    BinaryPairFrame.Preserves pointChart (row58Generators i) (redundantCyclicTops i) := by
  unfold BinaryPairFrame.Preserves; decide +kernel
theorem row105_preserves : ∀ i,
    BinaryPairFrame.Preserves pointChart (row105Generators i) (cyclicTops i) := by
  unfold BinaryPairFrame.Preserves; decide +kernel
theorem row285_preserves : ∀ i,
    BinaryPairFrame.Preserves pointChart (row285Generators i) (secondSymmetricTops i) := by
  unfold BinaryPairFrame.Preserves; decide +kernel

def row58Frame : BinaryPairFrame Row58Top (Fin 6) :=
  BinaryPairFrame.ofGenerators pointChart row58Generators redundantCyclicTops row58_preserves
def row105Frame : BinaryPairFrame Row105Top (Fin 6) :=
  BinaryPairFrame.ofGenerators pointChart row105Generators cyclicTops row105_preserves
def row285Frame : BinaryPairFrame Row285Top (Fin 6) :=
  BinaryPairFrame.ofGenerators pointChart row285Generators secondSymmetricTops row285_preserves

theorem redundantCyclicTops_le :
    Subgroup.closure (Set.range redundantCyclicTops) ≤ Subgroup.zpowers cycle := by
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨i,rfl⟩
  fin_cases i
  · exact Subgroup.one_mem _
  · exact Subgroup.one_mem _
  · exact Subgroup.mem_zpowers cycle

theorem row58AtTwo_quotientSocle (N : Subgroup Row58Top) [N.Normal] :
    SocleNormalGeneratorBound (Row58Top ⧸ N) 2 := by
  apply cyclic_quotientSocle row58Frame (closureGenerators row58Generators 2)
    (BinaryPairFrame.ofGenerators_top_generator pointChart row58Generators
      redundantCyclicTops row58_preserves 2) ?_ N
  rw [show row58Frame.top.range = Subgroup.closure (Set.range redundantCyclicTops) from
    BinaryPairFrame.ofGenerators_top_range pointChart row58Generators
      redundantCyclicTops row58_preserves]
  exact redundantCyclicTops_le

theorem row105AtTwo_quotientSocle (N : Subgroup Row105Top) [N.Normal] :
    SocleNormalGeneratorBound (Row105Top ⧸ N) 2 := by
  apply cyclic_quotientSocle row105Frame (closureGenerators row105Generators 1)
    (BinaryPairFrame.ofGenerators_top_generator pointChart row105Generators
      cyclicTops row105_preserves 1) ?_ N
  rw [show row105Frame.top.range = Subgroup.closure (Set.range cyclicTops) from
    BinaryPairFrame.ofGenerators_top_range pointChart row105Generators cyclicTops row105_preserves]
  exact cyclicTops_le

theorem row285AtTwo_quotientSocle (N : Subgroup Row285Top) [N.Normal] :
    SocleNormalGeneratorBound (Row285Top ⧸ N) 2 :=
  symmetric_quotientSocle row285Frame
    (closureGenerators row285Generators 2) (closureGenerators row285Generators 1)
    (BinaryPairFrame.ofGenerators_top_generator pointChart row285Generators
      secondSymmetricTops row285_preserves 2)
    (BinaryPairFrame.ofGenerators_top_generator pointChart row285Generators
      secondSymmetricTops row285_preserves 1) N

def row58AtTwo_family : row58Interface.normalRegistry.QuotientSocleGeneratorFamily 2 :=
  FiniteNormalStateRegistry.QuotientSocleGeneratorFamily.ofQuotientBounds
    row58Interface.normalRegistry (fun N => by letI := N.2; exact row58AtTwo_quotientSocle N.1)
def row105AtTwo_family : row105Interface.normalRegistry.QuotientSocleGeneratorFamily 2 :=
  FiniteNormalStateRegistry.QuotientSocleGeneratorFamily.ofQuotientBounds
    row105Interface.normalRegistry (fun N => by letI := N.2; exact row105AtTwo_quotientSocle N.1)
def row285AtTwo_family : row285Interface.normalRegistry.QuotientSocleGeneratorFamily 2 :=
  FiniteNormalStateRegistry.QuotientSocleGeneratorFamily.ofQuotientBounds
    row285Interface.normalRegistry (fun N => by letI := N.2; exact row285AtTwo_quotientSocle N.1)

end SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveSixPairAlternateSocles

end
