import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateLatticeWord
import SymmetricSubgroupAsymptotics.CFSGExceptionalNormTwoBases
import SymmetricSubgroupAsymptotics.CFSGSerreConcreteDiagrams

/-! A bounded opposition certificate for the two ReeF4 relative words.
The nine-letter block is evaluated once in six integer coordinates;
its fourth power is negative E6 diagram reversal. No word census or
recognition of the whole exceptional-fixed positive group is used. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical Matrix
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourRelativeOppositionLattice
open CFSGExceptionalNormTwoBases CFSGExceptionalCartanPositiveDefinite
open CFSGNormTwoCoordinateLatticeWord CFSGNormTwoGeckWeylLatticeLinear
open CFSGNormTwoGeckWeylWordDegree CFSGSignedCartanReflections CFSGSerreDiagram

def relativeCoxeterWord : List (Fin 6) := [0,5,1,2,4,3,2,4,3]

def relativeOppositionWord : List (Fin 6) :=
  relativeCoxeterWord++relativeCoxeterWord++relativeCoxeterWord++relativeCoxeterWord

private def blockMatrix : Matrix (Fin 6) (Fin 6) ℤ :=
  !![0,1,0,0,-1,1;
     1,1,0,-1,0,1;
     1,1,0,0,-1,1;
     1,2,0,-1,0,1;
     1,1,-1,0,0,1;
     1,1,-1,0,0,0]

private theorem latticeWord_append (u v : List (Fin 6)) :
    latticeWord CartanMatrix.E₆ (u++v)=
      latticeWord CartanMatrix.E₆ u*latticeWord CartanMatrix.E₆ v := by
  induction u with
  | nil=>simp only [List.nil_append,latticeWord,one_mul]
  | cons i u ih=>simp only [List.cons_append,latticeWord,ih,mul_assoc]

private theorem blockMatrix_word :
    latticeWord CartanMatrix.E₆ relativeCoxeterWord=blockMatrix := by
  decide

private theorem opposition_matrix :
    latticeWord CartanMatrix.E₆ relativeOppositionWord=blockMatrix^4 := by
  rw [relativeOppositionWord]
  simp only [latticeWord_append,blockMatrix_word]
  noncomm_ring

private theorem fourth_column (i : Fin 6) :
    blockMatrix^4*ᵥ(Pi.single i (1:ℤ) : Fin 6→ℤ)=
      -(Pi.single (e6Permutation i) (1:ℤ) : Fin 6→ℤ) := by
  fin_cases i <;> decide

theorem relative_opposition_simple_lattice (i : Fin 6) :
    latticeWord CartanMatrix.E₆ relativeOppositionWord*ᵥ(Pi.single i (1:ℤ) : Fin 6→ℤ)=
      -(Pi.single (e6Permutation i) (1:ℤ) : Fin 6→ℤ) := by
  rw [opposition_matrix]
  exact fourth_column i

private theorem relative_opposition_linear_simple (i : Fin 6) :
    wordLinear CartanMatrix.E₆ CartanMatrix.E₆_transpose E6_positive_definite
      E6Base E6Index relativeOppositionWord
        (E6Index i : CFSGNormTwoRootPairing.Roots CartanMatrix.E₆).val=
      -(Pi.single (e6Permutation i) (1:ℤ) : Fin 6→ℤ) := by
  have h := LinearMap.congr_fun (latticeWord_linear CartanMatrix.E₆ CartanMatrix.E₆_diag
    CartanMatrix.E₆_transpose E6_positive_definite CartanMatrix.E₆_off_diag_nonpos
      relativeOppositionWord) (Pi.single i (1:ℤ) : Fin 6→ℤ)
  change latticeWord CartanMatrix.E₆ relativeOppositionWord*ᵥ(Pi.single i (1:ℤ) : Fin 6→ℤ)=
    wordLinear CartanMatrix.E₆ CartanMatrix.E₆_transpose E6_positive_definite
      E6Base E6Index relativeOppositionWord (Pi.single i (1:ℤ) : Fin 6→ℤ) at h
  rw [relative_opposition_simple_lattice] at h
  exact h.symm

theorem relative_opposition_simple_nonpositive (i j : Fin 6) :
    (wordRoot CartanMatrix.E₆ CartanMatrix.E₆_transpose E6_positive_definite
      E6Base E6Index relativeOppositionWord (E6Index i)).val j≤0 := by
  have h := (wordLinear_root CartanMatrix.E₆ CartanMatrix.E₆_transpose E6_positive_definite
    E6Base E6Index relativeOppositionWord (E6Index i)).symm.trans
      (relative_opposition_linear_simple i)
  rw [h]
  change -(Pi.single (e6Permutation i) (1:ℤ) : Fin 6→ℤ) j≤0
  simp only [Pi.single_apply]
  split_ifs <;> norm_num

end SymmetricSubgroupAsymptotics.CFSGReeFFourRelativeOppositionLattice
