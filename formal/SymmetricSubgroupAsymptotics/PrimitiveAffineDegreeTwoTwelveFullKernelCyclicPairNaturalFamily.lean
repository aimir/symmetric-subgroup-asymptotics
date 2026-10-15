import SymmetricSubgroupAsymptotics.BinaryPairFullKernelWords
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveSymmetricPairNaturalFamily
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveEvenTwoTernaryPairNaturalFamily
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelvePairFiniteCatalogueRows201To250

/-! Four full-kernel original actions share cyclic pair-module bounds.
A single displayed flip and prescribed transports produce all six
individual flips. The full-kernel theorem retains natural capacity one. -/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveFullKernelCyclicPairNaturalFamily

open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
open DegreeTwoTwelvePairFiniteCatalogue

abbrev pointChart := PrimitiveAffineDegreeTwoTwelveFullPairKernelNaturalFamily.pointChart

theorem uniform_one {m : ℕ} (gs : Fin m → Equiv.Perm (Fin 12))
    (tops : Fin m → Equiv.Perm (Fin 6)) (ki : Fin m)
    (q : Fin 6 → Subgroup.closure (Set.range gs))
    (hp : ∀ i, BinaryPairFrame.Preserves pointChart (gs i) (tops i))
    (hk : tops ki = 1)
    (hq : ∀ i : Fin 6,
      (pointChart.symm ((q i : Equiv.Perm (Fin 12)) (pointChart (0, 0)))).1 = i)
    (hbits : ∀ i x : Fin 6,
      (pointChart.symm
        (((q i * closureGenerators gs ki * (q i)⁻¹ : Subgroup.closure (Set.range gs)) :
          Equiv.Perm (Fin 12)) (pointChart (x, 0)))).2 =
            (Pi.single i 1 : Fin 6 → ZMod 2) x)
    (hpair : UniformSubrepresentationGeneratorBound
      (permutationFunctionRepresentation (ZMod 2)
        (BinaryPairFrame.ofGenerators pointChart gs tops hp).top.range (Fin 6)) 1) :
    UniformSubrepresentationGeneratorBound
      (permutationFunctionRepresentation (ZMod 2)
        (Subgroup.closure (Set.range gs)) (Fin 12)) 1 := by
  let F := BinaryPairFrame.ofGenerators pointChart gs tops hp
  apply F.uniform_of_full_pair_kernel_words 0 (closureGenerators gs ki) q
  · exact (BinaryPairFrame.ofGenerators_top_generator pointChart gs tops hp ki).trans hk
  · intro i
    exact (F.intertwine (q i) (0, 0)).symm.trans (hq i)
  · exact hbits
  · exact hpair

open BinarySixPointSymmetricMatrixBlocks in
def row135Tops : Fin 3 → Equiv.Perm (Fin 6) := ![1, rotation, reflection]

open BinarySixPointSymmetricMatrixBlocks PrimitiveAffineDegreeTwoTwelveSymmetricPairNaturalFamily in
def row224Tops : Fin 4 → Equiv.Perm (Fin 6) := ![1, kleinMover, rotation, oddMover]

open BinaryTwoTernaryPairOperator in
def row240Tops : Fin 4 → Equiv.Perm (Fin 6) :=
  ![1, rotation, PrimitiveAffineDegreeTwoTwelveTwoTernaryPairNaturalFamily.reflection, mover 1]

open BinaryTwoTernaryPairOperator in
def row241Tops : Fin 4 → Equiv.Perm (Fin 6) :=
  ![1, rotation, PrimitiveAffineDegreeTwoTwelveTwoTernaryPairNaturalFamily.reflection, mover 0]

theorem row135Natural : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) row135Interface.top (Fin 12)) 1 := by
  let c := closureGenerators row135Generators 1
  let b := closureGenerators row135Generators 2
  let hp : ∀ i, BinaryPairFrame.Preserves pointChart (row135Generators i) (row135Tops i) := by
    unfold BinaryPairFrame.Preserves
    decide +kernel
  apply uniform_one row135Generators row135Tops 0
    (PrimitiveAffineDegreeTwoTwelveSymmetricPairNaturalFamily.transportWords c b) hp
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · exact PrimitiveAffineDegreeTwoTwelveSymmetricPairNaturalFamily.pair_uniform
      row135Generators row135Tops hp c b (by decide +kernel) (by decide +kernel)

theorem row224Natural : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) row224Interface.top (Fin 12)) 1 := by
  let c := closureGenerators row224Generators 2
  let b := c * closureGenerators row224Generators 1 * closureGenerators row224Generators 3
  let hp : ∀ i, BinaryPairFrame.Preserves pointChart (row224Generators i) (row224Tops i) := by
    unfold BinaryPairFrame.Preserves
    decide +kernel
  apply uniform_one row224Generators row224Tops 0
    (PrimitiveAffineDegreeTwoTwelveSymmetricPairNaturalFamily.transportWords c b) hp
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · exact PrimitiveAffineDegreeTwoTwelveSymmetricPairNaturalFamily.pair_uniform
      row224Generators row224Tops hp c b (by decide +kernel) (by decide +kernel)

theorem row240Natural : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) row240Interface.top (Fin 12)) 1 := by
  let t := closureGenerators row240Generators 1
  let c := closureGenerators row240Generators 3
  let hp : ∀ i, BinaryPairFrame.Preserves pointChart (row240Generators i) (row240Tops i) := by
    unfold BinaryPairFrame.Preserves
    decide +kernel
  apply uniform_one row240Generators row240Tops 0
    (PrimitiveAffineDegreeTwoTwelveEvenTwoTernaryPairNaturalFamily.transportWord 1 t c) hp
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · exact PrimitiveAffineDegreeTwoTwelveTwoTernaryPairNaturalFamily.pair_uniform
      1 row240Generators row240Tops 1 3 hp (by decide +kernel) (by decide +kernel)

theorem row241Natural : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) row241Interface.top (Fin 12)) 1 := by
  let t := closureGenerators row241Generators 1
  let c := closureGenerators row241Generators 3
  let hp : ∀ i, BinaryPairFrame.Preserves pointChart (row241Generators i) (row241Tops i) := by
    unfold BinaryPairFrame.Preserves
    decide +kernel
  apply uniform_one row241Generators row241Tops 0
    (PrimitiveAffineDegreeTwoTwelveEvenTwoTernaryPairNaturalFamily.transportWord 0 t c) hp
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · exact PrimitiveAffineDegreeTwoTwelveTwoTernaryPairNaturalFamily.pair_uniform
      0 row241Generators row241Tops 1 3 hp (by decide +kernel) (by decide +kernel)

end SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveFullKernelCyclicPairNaturalFamily

end
