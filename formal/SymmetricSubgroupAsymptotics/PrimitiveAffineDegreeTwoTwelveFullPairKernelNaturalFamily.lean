import SymmetricSubgroupAsymptotics.BinaryPairFullKernelGenerators
import SymmetricSubgroupAsymptotics.BinaryPairFrameGenerators
import SymmetricSubgroupAsymptotics.LiteralCyclicOrbitWitness
import SymmetricSubgroupAsymptotics.PermutationNaturalBoundPointEmbedding
import SymmetricSubgroupAsymptotics.DerivedGeneratorWords
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelvePairFiniteCatalogueRows151To200
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelvePairFiniteCatalogueRows201To250

/-! Two original capacity-two natural bounds from a full physical pair
kernel. Six displayed conjugates of the original first generator flip the
six individual pairs. The induced ternary shift has exactly the two
displayed point orbits. Row227 contains the same original generators. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SymmetricSubgroupAsymptotics
namespace PrimitiveAffineDegreeTwoTwelveFullPairKernelNaturalFamily

open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
open DegreeTwoTwelvePairFiniteCatalogue

def pointChart : Fin 6 × ZMod 2 ≃ Fin 12 where
  toFun p := if p.2 = 0 then ![0, 1, 3, 5, 7, 9] p.1 else ![11, 2, 4, 6, 8, 10] p.1
  invFun x := (![0, 1, 1, 2, 2, 3, 3, 4, 4, 5, 5, 0] x,
    ![0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1] x)
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pairDoubleSwap : Equiv.Perm (Fin 6) where
  toFun := ![0, 4, 5, 3, 1, 2]
  invFun := ![0, 4, 5, 3, 1, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pairShift : Equiv.Perm (Fin 6) where
  toFun := ![2, 3, 4, 5, 0, 1]
  invFun := ![4, 5, 0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def topGenerators : Fin 3 → Equiv.Perm (Fin 6) := ![1, pairDoubleSwap, pairShift]

theorem generators_preserve : ∀ i,
    BinaryPairFrame.Preserves pointChart (row188Generators i) (topGenerators i) := by
  unfold BinaryPairFrame.Preserves
  decide +kernel

def pairFrame : BinaryPairFrame Row188Top (Fin 6) :=
  BinaryPairFrame.ofGenerators pointChart row188Generators topGenerators generators_preserve

def g (i : Fin 3) : Row188Top := closureGenerators row188Generators i

theorem top_generator (i : Fin 3) : pairFrame.top (g i) = topGenerators i :=
  BinaryPairFrame.ofGenerators_top_generator pointChart row188Generators topGenerators
    generators_preserve i

/-- Prescribed words sending pair zero to each of the six pairs. -/
def transport : Fin 6 → Row188Top :=
  ![1, g 2 * g 1 * g 2, g 2, g 2 ^ 2 * g 1 * g 2, g 2 ^ 2, g 1 * g 2]

theorem transport_zero (i : Fin 6) : pairFrame.top (transport i) 0 = i := by
  have hpoint : ∀ j : Fin 6,
      (pointChart.symm ((transport j : Equiv.Perm (Fin 12)) (pointChart (0, 0)))).1 = j := by
    decide +kernel
  exact (pairFrame.intertwine (transport i) (0, 0)).symm.trans (hpoint i)

theorem pair_transitive (i j : Fin 6) :
    ∃ u : Row188Top, pairFrame.top u i = j := by
  refine ⟨transport j * (transport i)⁻¹, ?_⟩
  rw [map_mul, map_inv]
  change pairFrame.top (transport j) ((pairFrame.top (transport i))⁻¹ i) = j
  have hi : (pairFrame.top (transport i))⁻¹ i = 0 := by
    calc
      _ = (pairFrame.top (transport i))⁻¹ (pairFrame.top (transport i) 0) :=
        congrArg (fun x ↦ (pairFrame.top (transport i))⁻¹ x) (transport_zero i).symm
      _ = 0 := (pairFrame.top (transport i)).symm_apply_apply 0
  rw [hi]
  exact transport_zero j

def baseFlip : pairFrame.top.ker :=
  ⟨g 0, by change pairFrame.top (g 0) = 1; exact top_generator 0⟩

def localFlip (i : Fin 6) : pairFrame.top.ker :=
  MulAut.conjNormal (transport i) baseFlip

theorem localFlip_bits (i : Fin 6) :
    pairFrame.bits (localFlip i) = Pi.single i (1 : ZMod 2) := by
  have hpoint : ∀ i j : Fin 6,
      (pointChart.symm
        (((transport i * g 0 * (transport i)⁻¹ : Row188Top) : Equiv.Perm (Fin 12))
          (pointChart (j, 0)))).2 = (Pi.single i 1 : Fin 6 → ZMod 2) j := by
    decide +kernel
  funext j
  exact hpoint i j

def pairOrbitWitness : LiteralCyclicOrbitWitness pairFrame.top.range 2 where
  element := pairFrame.top.rangeRestrict (g 2)
  representative := ![0, 1]
  orbitIndex := ![0, 1, 0, 1, 0, 1]
  exponent := ![0, 0, 1, 1, 2, 2]
  point_eq := by
    change ∀ x : Fin 6,
      (pairFrame.top (g 2) ^ (![0, 0, 1, 1, 2, 2] x : Fin 6).val)
        (![0, 1] (![0, 1, 0, 1, 0, 1] x : Fin 2)) = x
    rw [top_generator]
    decide +kernel

theorem row188Natural : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) row188Interface.top (Fin 12)) 2 :=
  pairFrame.uniform_of_full_pair_kernel_coordinateTop
    (fun i ↦ ⟨localFlip i, localFlip_bits i⟩) pair_transitive 2
    (pairOrbitWitness.uniform _)

def row227Embedding : LiteralPermutationGeneratorEmbedding row188Generators Row227Top where
  pointEquiv := Equiv.refl _
  images := ![closureGenerators row227Generators 0,
    closureGenerators row227Generators 1, closureGenerators row227Generators 2]
  point_eq := by decide +kernel

theorem row227Natural : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) row227Interface.top (Fin 12)) 2 :=
  row227Embedding.uniform row188Natural

end PrimitiveAffineDegreeTwoTwelveFullPairKernelNaturalFamily
end SymmetricSubgroupAsymptotics

end
