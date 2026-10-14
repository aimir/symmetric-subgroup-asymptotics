import SymmetricSubgroupAsymptotics.InvariantEmbeddingPermutationAction
import SymmetricSubgroupAsymptotics.BinaryFourAffineImage
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPrimitiveSixteenRows8And10LinearRelations
import Mathlib.Tactic.Group

/-! Fifteen explicit Fano heptads, with the empty configuration as zero.
Each Fano triple is represented by an unordered partition of eight labels
into complementary four-sets. This makes the action of all eight-label
permutations functorial. The chart is bound to the original row20 action,
and the displayed binary change of basis binds the original row11 action.
Only these fixed configurations and four-bit formulas are checked here.

The construction is motivated by Godsil, Finite Geometry, section4.4;
no theorem from that source is a hypothesis of this module. -/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace BinaryFanoHeptadData

open BinaryFourAffineImage
open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer

abbrev Label := Fin 8
abbrev Quad := Finset Label
abbrev Partition := Finset Quad
abbrev Heptad := Finset Partition

def alpha : Equiv.Perm Label := Equiv.swap 0 1 * Equiv.swap 1 2
def gamma : Equiv.Perm Label := Equiv.swap 7 0 * Equiv.swap 0 1
def beta : Equiv.Perm Label where
  toFun i := ![1, 2, 3, 4, 5, 6, 0, 7] i
  invFun i := ![6, 0, 1, 2, 3, 4, 5, 7] i
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def partition (s : Quad) : Partition := {s, Finset.univ \ s}

def heptadAction : Equiv.Perm Label →* Equiv.Perm Heptad :=
  (InvariantEmbeddingPermutationAction.finsetHom Partition).comp
    ((InvariantEmbeddingPermutationAction.finsetHom Quad).comp
      (InvariantEmbeddingPermutationAction.finsetHom Label))

/-- The cyclic Fano plane on labels0,...,6, with label7 adjoined to
each triple when forming its four-set partition. -/
def base : Heptad :=
  {partition {7, 0, 1, 3}, partition {7, 1, 2, 4},
   partition {7, 2, 3, 5}, partition {7, 3, 4, 6},
   partition {7, 0, 4, 5}, partition {7, 1, 5, 6},
   partition {7, 0, 2, 6}}

def plus (k : ℕ) : Heptad := heptadAction (beta ^ k * alpha) base
def minus (k : ℕ) : Heptad := heptadAction (beta ^ k * alpha⁻¹) base

/-- Labels are the original binary masks, with the two seven-orbits
read directly from row20 generator one. -/
def configuration (i : Fin 16) : Heptad :=
  ![∅, plus 6, plus 1, minus 2, plus 0, minus 4, minus 5, plus 3,
    base, minus 6, minus 1, plus 2, minus 0, plus 4, plus 5, minus 3] i

abbrev a20 : LinearGroup :=
  PrimitiveAffineDegreeTwoPrimitiveSixteenRows8And10LinearRelations.a

def b20 : LinearGroup where
  toFun v := ![v 1, v 1 + v 2, v 0, v 1 + v 3]
  invFun v := ![v 2, v 0, v 0 + v 1, v 0 + v 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel
  map_add' := by decide +kernel
  map_smul' := by decide +kernel

def a11 : LinearGroup where
  toFun v := ![v 0 + v 1, v 2, v 0, v 0 + v 3]
  invFun v := ![v 2, v 0 + v 2, v 1, v 2 + v 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel
  map_add' := by decide +kernel
  map_smul' := by decide +kernel

def b11 : LinearGroup where
  toFun v := ![v 0 + v 1, v 0, v 0 + v 1 + v 2 + v 3, v 1 + v 2]
  invFun v := ![v 1, v 0 + v 1, v 0 + v 1 + v 3, v 1 + v 2 + v 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel
  map_add' := by decide +kernel
  map_smul' := by decide +kernel

/-- Columns[1,7,13,8] transport the heptad coordinates to row11. -/
def chart11 : LinearGroup where
  toFun v := ![v 0 + v 1 + v 2, v 1, v 1 + v 2, v 2 + v 3]
  invFun v := ![v 0 + v 2, v 1, v 1 + v 2, v 1 + v 2 + v 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel
  map_add' := by decide +kernel
  map_smul' := by decide +kernel

def gammaLinear : LinearGroup := chart11⁻¹ * b11 * chart11

theorem a20_original : linearPerm a20 = DegreeTwoPrimitiveSixteenInterfaces.row20Generators 0 :=
  PrimitiveAffineDegreeTwoPrimitiveSixteenRows8And10LinearRelations.linearPerm_a_row8
theorem b20_original : linearPerm b20 = DegreeTwoPrimitiveSixteenInterfaces.row20Generators 1 := by
  apply Equiv.ext; intro x; revert x; decide +kernel
theorem a11_original : linearPerm a11 = DegreeTwoPrimitiveSixteenInterfaces.row11Generators 0 := by
  apply Equiv.ext; intro x; revert x; decide +kernel
theorem b11_original : linearPerm b11 = DegreeTwoPrimitiveSixteenInterfaces.row11Generators 1 := by
  apply Equiv.ext; intro x; revert x; decide +kernel

theorem chart11_beta : chart11 * b20 * chart11⁻¹ = a11 := by
  apply LinearEquiv.ext; intro v; revert v; decide +kernel
theorem chart11_gamma : chart11 * gammaLinear * chart11⁻¹ = b11 := by
  dsimp [gammaLinear]
  group

theorem configuration_injective : Function.Injective configuration := by decide +kernel

theorem alpha_configuration : ∀ i, heptadAction alpha (configuration i) =
    configuration (linearPerm a20 i) := by
  intro i; fin_cases i <;> decide +kernel

theorem beta_configuration : ∀ i, heptadAction beta (configuration i) =
    configuration (linearPerm b20 i) := by
  intro i; fin_cases i <;> decide +kernel

theorem gamma_configuration : ∀ i, heptadAction gamma (configuration i) =
    configuration (linearPerm gammaLinear i) := by
  intro i; fin_cases i <;> decide +kernel

end BinaryFanoHeptadData
end SymmetricSubgroupAsymptotics

end
