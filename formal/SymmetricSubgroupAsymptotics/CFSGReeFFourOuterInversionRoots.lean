import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateOutsideWordPositive
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinatePositiveRootGenerators
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateOrthogonalRootSupport
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateLatticeWord
import SymmetricSubgroupAsymptotics.CFSGExceptionalNormTwoBases
import SymmetricSubgroupAsymptotics.CFSGExceptionalCartanPositiveDefinite

/-! The inversion roots of the literal outer paired word are exactly
its three orthogonal E6 simple roots. Outside coordinates are unchanged,
and norm two identifies the supported positive root. No root census or
coefficient-field hypothesis is used. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical Matrix
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourOuterInversionRoots
open CFSGNormTwoRootPairing CFSGIntegerMatrixPairing CFSGExceptionalNormTwoBases
open CFSGExceptionalCartanPositiveDefinite
open CFSGNormTwoCoordinateOutsideWordPositive CFSGNormTwoCoordinateOrthogonalRootSupport
open CFSGNormTwoGeckWeylWordDegree CFSGNormTwoGeckWeylLatticeLinear
open CFSGNormTwoCoordinateLatticeWord CFSGSignedCartanReflections CFSGIntegralNormTwoSigns
open CFSGNormTwoCoordinatePositiveRootGenerators
local notation "A" => CartanMatrix.E₆
local notation "hd" => CartanMatrix.E₆_diag
local notation "hs" => CartanMatrix.E₆_transpose
local notation "hp" => E6_positive_definite
local notation "ho" => CartanMatrix.E₆_off_diag_nonpos
local notation "b₀" => coordinateBase A hd hs hp ho
local notation "s₀" => coordinateIndexEquiv A hd hs hp ho
local instance : DecidableEq (Roots A) := Classical.decEq _

def blockWord : List (Fin 6) := [0,5,1]
def blockNodes : Finset (Fin 6) := {0,1,5}

private theorem nodes_orthogonal :
    ∀i∈blockNodes,∀j∈blockNodes,i≠j→A j i=0 := by decide +kernel

private theorem word_mem_nodes : ∀i : Fin 6,i∈blockWord↔i∈blockNodes := by decide +kernel

private theorem simple_lattice_negative : ∀i : Fin 6,i∈blockNodes→
    latticeWord A blockWord*ᵥ(Pi.single i (1:ℤ) : Fin 6→ℤ)= -Pi.single i (1:ℤ) := by
  decide +kernel

theorem outer_word_simple_val (i : Fin 6) (hi : i∈blockNodes) :
    (wordRoot A hs hp b₀ s₀ blockWord (coordinateRoot A hd i)).val=
      -(Pi.single i (1:ℤ) : Fin 6→ℤ) := by
  have he := LinearMap.congr_fun (latticeWord_linear A hd hs hp ho blockWord)
    (coordinateRoot A hd i).val
  change latticeWord A blockWord*ᵥ(coordinateRoot A hd i).val=
    wordLinear A hs hp b₀ s₀ blockWord (coordinateRoot A hd i).val at he
  rw [wordLinear_root] at he
  exact he.symm.trans (simple_lattice_negative i hi)

theorem outer_negative_iff (k : PositiveRoot A) :
    (¬∀j,0≤(wordRoot A hs hp b₀ s₀ blockWord k.val).val j) ↔
      ∃i∈blockNodes,k.val=coordinateRoot A hd i := by
  constructor
  · intro hk
    have hn := (norm_two_coordinates_one_sign A hs hp
      (fun i=>by rw [hd i];exact even_two) ho _
      (wordRoot A hs hp b₀ s₀ blockWord k.val).property).resolve_left hk
    have hsupport : ∀j,j∉blockNodes→k.val.val j=0 := by
      intro j hj
      have hw : ∀i∈blockWord,i≠j := by
        intro i hi hij
        subst j
        exact hj ((word_mem_nodes i).mp hi)
      have he := wordRoot_outside_coordinate A hd hs hp ho blockWord k.val j hw
      have hnonpos := hn j
      rw [he] at hnonpos
      have hnonneg := k.property j
      omega
    exact positive_root_supported_on_orthogonal_simples A hd hs hp
      {i | i∈blockNodes} nodes_orthogonal k.val k.property hsupport
  · rintro ⟨i,hi,he⟩ hk
    have hnonneg := hk i
    rw [he,outer_word_simple_val i hi] at hnonneg
    simp only [Pi.neg_apply,Pi.single_eq_same] at hnonneg
    omega

end SymmetricSubgroupAsymptotics.CFSGReeFFourOuterInversionRoots
