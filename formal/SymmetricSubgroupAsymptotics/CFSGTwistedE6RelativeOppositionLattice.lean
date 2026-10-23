import SymmetricSubgroupAsymptotics.CFSGTwistedE6FixedWordClassification
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateLatticeWord

/-! One explicit relative opposition word. Its 36-letter E6 expansion
sends each simple lattice vector to the negative diagram partner. This
is a six-column finite certificate, not a Weyl-group enumeration. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical Matrix
namespace SymmetricSubgroupAsymptotics.CFSGTwistedE6RelativeOppositionLattice
open CFSGTwistedE6FixedWordClassification CFSGTwistedE6WeylChamber
open CFSGExceptionalNormTwoBases CFSGExceptionalCartanPositiveDefinite
open CFSGNormTwoCoordinateLatticeWord CFSGNormTwoGeckWeylLatticeLinear
open CFSGNormTwoGeckWeylWordDegree CFSGSignedCartanReflections CFSGSerreDiagram

def oppositionRelativeWord : List (Fin 4) :=
  [0,1,2,3,0,1,2,3,0,1,2,3,0,1,2,3,0,1,2,3,0,1,2,3]

def oppositionWord : List (Fin 6) := expandRelative oppositionRelativeWord

private def coxeterWord : List (Fin 6) := [0,5,2,4,3,1]

private def coxeterMatrix : Matrix (Fin 6) (Fin 6) ℤ :=
  !![0, -1, 0, 0, 1, 0;
    0, -1, 0, 1, 0, 0;
    1, -1, 0, 0, 1, 0;
    0, -1, 1, 0, 1, 0;
    0, -1, 1, 0, 0, 1;
    0, -1, 1, 0, 0, 0]

private theorem latticeWord_append (u v : List (Fin 6)) :
    latticeWord CartanMatrix.E₆ (u++v)=
      latticeWord CartanMatrix.E₆ u*latticeWord CartanMatrix.E₆ v := by
  induction u with
  | nil=>simp only [List.nil_append,latticeWord,one_mul]
  | cons i u ih=>simp only [List.cons_append,latticeWord,ih,mul_assoc]

private theorem coxeterMatrix_word : latticeWord CartanMatrix.E₆ coxeterWord=coxeterMatrix := by
  decide

private theorem opposition_matrix :
    latticeWord CartanMatrix.E₆ oppositionWord=coxeterMatrix^6 := by
  have hw : oppositionWord=coxeterWord++coxeterWord++coxeterWord++
      coxeterWord++coxeterWord++coxeterWord := rfl
  rw [hw]
  simp only [latticeWord_append,coxeterMatrix_word]
  noncomm_ring

private theorem coxeter_sixth_column (i : Fin 6) :
    coxeterMatrix^6*ᵥ(Pi.single i (1 : ℤ) : Fin 6→ℤ)=
      -(Pi.single (e6Permutation i) (1 : ℤ) : Fin 6→ℤ) := by
  fin_cases i <;> decide

theorem opposition_simple_lattice (i : Fin 6) :
    latticeWord CartanMatrix.E₆ oppositionWord*ᵥ(Pi.single i (1 : ℤ) : Fin 6→ℤ)=
      -(Pi.single (e6Permutation i) (1 : ℤ) : Fin 6→ℤ) := by
  rw [opposition_matrix]
  exact coxeter_sixth_column i

theorem opposition_linear_simple (i : Fin 6) :
    wordLinear CartanMatrix.E₆ CartanMatrix.E₆_transpose E6_positive_definite
      E6Base E6Index oppositionWord (E6Index i : CFSGNormTwoRootPairing.Roots CartanMatrix.E₆).val=
      -(Pi.single (e6Permutation i) (1 : ℤ) : Fin 6→ℤ) := by
  have h := LinearMap.congr_fun (latticeWord_linear CartanMatrix.E₆ CartanMatrix.E₆_diag
    CartanMatrix.E₆_transpose E6_positive_definite CartanMatrix.E₆_off_diag_nonpos oppositionWord)
      (Pi.single i (1 : ℤ) : Fin 6→ℤ)
  change latticeWord CartanMatrix.E₆ oppositionWord*ᵥ(Pi.single i (1 : ℤ) : Fin 6→ℤ)=
    wordLinear CartanMatrix.E₆ CartanMatrix.E₆_transpose E6_positive_definite
      E6Base E6Index oppositionWord (Pi.single i (1 : ℤ) : Fin 6→ℤ) at h
  rw [opposition_simple_lattice] at h
  exact h.symm

theorem opposition_simple_nonpositive (i j : Fin 6) :
    (wordRoot CartanMatrix.E₆ CartanMatrix.E₆_transpose E6_positive_definite
      E6Base E6Index oppositionWord (E6Index i)).val j≤0 := by
  have h := (wordLinear_root CartanMatrix.E₆ CartanMatrix.E₆_transpose E6_positive_definite
    E6Base E6Index oppositionWord (E6Index i)).symm.trans (opposition_linear_simple i)
  rw [h]
  change -(Pi.single (e6Permutation i) (1 : ℤ) : Fin 6→ℤ) j≤0
  simp only [Pi.single_apply]
  split_ifs <;> norm_num

end SymmetricSubgroupAsymptotics.CFSGTwistedE6RelativeOppositionLattice
