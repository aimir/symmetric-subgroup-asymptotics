import SymmetricSubgroupAsymptotics.SixPairCyclicSymmetricSocles
import SymmetricSubgroupAsymptotics.DerivedGeneratorWords
import SymmetricSubgroupAsymptotics.FiniteNormalRegistrySocleOfQuotientBounds
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelvePairFiniteCatalogueRows51To100
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelvePairFiniteCatalogueRows101To150
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelvePairFiniteCatalogueRows201To250
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelvePairFiniteCatalogueRows251To301

/-! Four original joint capacity-two socle fields from one physical pair
kernel theorem. The retained six-point images are cyclic for 87/134 and
symmetric for 219/293. No affine splitting or flip-kernel expansion is used. -/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveSixPairImageSocles

open SixPairCyclicSymmetricSocles
open Non2UnipotentPrefixFiniteMenu
open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
open DegreeTwoTwelvePairFiniteCatalogue

def cyclicTops : Fin 2 → Equiv.Perm (Fin 6) := ![1,cycle]
def firstSymmetricTops : Fin 3 → Equiv.Perm (Fin 6) := ![swap,cycle,1]
def secondSymmetricTops : Fin 3 → Equiv.Perm (Fin 6) := ![1,swap,cycle]

theorem row87_preserves : ∀ i,
    BinaryPairFrame.Preserves pointChart (row87Generators i) (cyclicTops i) := by
  unfold BinaryPairFrame.Preserves; decide +kernel
theorem row134_preserves : ∀ i,
    BinaryPairFrame.Preserves pointChart (row134Generators i) (cyclicTops i) := by
  unfold BinaryPairFrame.Preserves; decide +kernel
theorem row219_preserves : ∀ i,
    BinaryPairFrame.Preserves pointChart (row219Generators i) (firstSymmetricTops i) := by
  unfold BinaryPairFrame.Preserves; decide +kernel
theorem row293_preserves : ∀ i,
    BinaryPairFrame.Preserves pointChart (row293Generators i) (secondSymmetricTops i) := by
  unfold BinaryPairFrame.Preserves; decide +kernel

def row87Frame : BinaryPairFrame Row87Top (Fin 6) :=
  BinaryPairFrame.ofGenerators pointChart row87Generators cyclicTops row87_preserves
def row134Frame : BinaryPairFrame Row134Top (Fin 6) :=
  BinaryPairFrame.ofGenerators pointChart row134Generators cyclicTops row134_preserves
def row219Frame : BinaryPairFrame Row219Top (Fin 6) :=
  BinaryPairFrame.ofGenerators pointChart row219Generators firstSymmetricTops row219_preserves
def row293Frame : BinaryPairFrame Row293Top (Fin 6) :=
  BinaryPairFrame.ofGenerators pointChart row293Generators secondSymmetricTops row293_preserves

theorem cyclicTops_le : Subgroup.closure (Set.range cyclicTops) ≤ Subgroup.zpowers cycle := by
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨i,rfl⟩
  fin_cases i
  · exact Subgroup.one_mem _
  · exact Subgroup.mem_zpowers cycle

theorem row87_quotientSocle (N : Subgroup Row87Top) [N.Normal] :
    SocleNormalGeneratorBound (Row87Top ⧸ N) 2 := by
  apply cyclic_quotientSocle row87Frame (closureGenerators row87Generators 1)
    (BinaryPairFrame.ofGenerators_top_generator pointChart row87Generators cyclicTops row87_preserves 1) ?_ N
  rw [show row87Frame.top.range = Subgroup.closure (Set.range cyclicTops) from
    BinaryPairFrame.ofGenerators_top_range pointChart row87Generators cyclicTops row87_preserves]
  exact cyclicTops_le

theorem row134_quotientSocle (N : Subgroup Row134Top) [N.Normal] :
    SocleNormalGeneratorBound (Row134Top ⧸ N) 2 := by
  apply cyclic_quotientSocle row134Frame (closureGenerators row134Generators 1)
    (BinaryPairFrame.ofGenerators_top_generator pointChart row134Generators cyclicTops row134_preserves 1) ?_ N
  rw [show row134Frame.top.range = Subgroup.closure (Set.range cyclicTops) from
    BinaryPairFrame.ofGenerators_top_range pointChart row134Generators cyclicTops row134_preserves]
  exact cyclicTops_le

theorem row219_quotientSocle (N : Subgroup Row219Top) [N.Normal] :
    SocleNormalGeneratorBound (Row219Top ⧸ N) 2 :=
  symmetric_quotientSocle row219Frame
    (closureGenerators row219Generators 1) (closureGenerators row219Generators 0)
    (BinaryPairFrame.ofGenerators_top_generator pointChart row219Generators firstSymmetricTops row219_preserves 1)
    (BinaryPairFrame.ofGenerators_top_generator pointChart row219Generators firstSymmetricTops row219_preserves 0) N

theorem row293_quotientSocle (N : Subgroup Row293Top) [N.Normal] :
    SocleNormalGeneratorBound (Row293Top ⧸ N) 2 :=
  symmetric_quotientSocle row293Frame
    (closureGenerators row293Generators 2) (closureGenerators row293Generators 1)
    (BinaryPairFrame.ofGenerators_top_generator pointChart row293Generators secondSymmetricTops row293_preserves 2)
    (BinaryPairFrame.ofGenerators_top_generator pointChart row293Generators secondSymmetricTops row293_preserves 1) N

def row87_family : row87Interface.normalRegistry.QuotientSocleGeneratorFamily 2 :=
  FiniteNormalStateRegistry.QuotientSocleGeneratorFamily.ofQuotientBounds
    row87Interface.normalRegistry (fun N => by letI := N.2; exact row87_quotientSocle N.1)
def row134_family : row134Interface.normalRegistry.QuotientSocleGeneratorFamily 2 :=
  FiniteNormalStateRegistry.QuotientSocleGeneratorFamily.ofQuotientBounds
    row134Interface.normalRegistry (fun N => by letI := N.2; exact row134_quotientSocle N.1)
def row219_family : row219Interface.normalRegistry.QuotientSocleGeneratorFamily 2 :=
  FiniteNormalStateRegistry.QuotientSocleGeneratorFamily.ofQuotientBounds
    row219Interface.normalRegistry (fun N => by letI := N.2; exact row219_quotientSocle N.1)
def row293_family : row293Interface.normalRegistry.QuotientSocleGeneratorFamily 2 :=
  FiniteNormalStateRegistry.QuotientSocleGeneratorFamily.ofQuotientBounds
    row293Interface.normalRegistry (fun N => by letI := N.2; exact row293_quotientSocle N.1)

end SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveSixPairImageSocles

end
