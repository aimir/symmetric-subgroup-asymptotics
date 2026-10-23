import SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckRelativeOpposition
import SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckRelativeWordEnvelope
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateLatticeWord

/-! Relative opposition commutes with each folded simple reflection on
the literal E6 lattice. Its actual matrix commutator with a folded Weyl
representative therefore belongs to the full simultaneous normalizer.
No assertion that this lattice-kernel factor is in the generated torus
or that the opposition matrix has square one is made. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical Matrix
namespace SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckOppositionSimpleRatio
open CFSGTwistedE6GeckRelativeOpposition CFSGTwistedE6RelativeOppositionLattice
open CFSGTwistedE6GeckRelativeWordEnvelope CFSGTwistedE6WeylChamber
open CFSGTwistedE6RelativeWeylOrbits CFSGTwistedE6FixedWordClassification
open CFSGTwistedE6GeckNormalizerEnvelope CFSGTwistedE6GeckDiagramCovariance
open CFSGExceptionalNormTwoBases CFSGExceptionalCartanPositiveDefinite
open CFSGNormTwoCoordinateLatticeWord CFSGNormTwoGeckIntegralWord
open CFSGNormTwoGeckWeylWordDegree
open CFSGNormTwoGeckWeylWordAlgebra CFSGSignedCartanReflections
open CFSGSerreDiagram CFSGSerreQuadraticWeylWord
local notation "A" => CartanMatrix.E₆

private def oppositionMatrix : Matrix (Fin 6) (Fin 6) ℤ :=
  fun i j=>-(Pi.single (e6Permutation j) (1:ℤ) : Fin 6→ℤ) i

private theorem opposition_lattice_matrix : latticeWord A oppositionWord=oppositionMatrix := by
  ext i j
  have h := congrFun (opposition_simple_lattice j) i
  simpa only [Matrix.mulVec_single_one,Matrix.col_apply] using h

private theorem opposition_matrix_commutes (a : Fin 4) :
    oppositionMatrix*latticeWord A (orbitWord a)=
      latticeWord A (orbitWord a)*oppositionMatrix := by
  fin_cases a <;> decide

private theorem action_commute_of_matrix (w v : List (Fin 6))
    (hm : latticeWord A w*latticeWord A v=latticeWord A v*latticeWord A w) :
    linearAction w*linearAction v=linearAction v*linearAction w := by
  have hl (u : List (Fin 6)) (x : Fin 6→ℤ) :
      latticeWord A u*ᵥx=linearAction u x :=
    LinearMap.congr_fun (latticeWord_linear A CartanMatrix.E₆_diag
      CartanMatrix.E₆_transpose E6_positive_definite CartanMatrix.E₆_off_diag_nonpos u) x
  apply LinearEquiv.ext
  intro x
  have h := congrArg (fun M : Matrix (Fin 6) (Fin 6) ℤ=>M*ᵥx) hm
  change linearAction w (linearAction v x)=linearAction v (linearAction w x)
  dsimp only at h
  rw [←Matrix.mulVec_mulVec,←Matrix.mulVec_mulVec] at h
  rw [hl v x,hl w (linearAction v x),hl w x,hl v (linearAction w x)] at h
  exact h

theorem opposition_orbit_action_commute (a : Fin 4) :
    linearAction oppositionWord*linearAction (orbitWord a)=
      linearAction (orbitWord a)*linearAction oppositionWord := by
  apply action_commute_of_matrix
  rw [opposition_lattice_matrix]
  exact opposition_matrix_commutes a

private theorem commutator_mem_of_action_commute (K : Type) [Field K]
    (w v : List (Fin 6)) (hc : linearAction w*linearAction v=linearAction v*linearAction w) :
    wordUnit A CartanMatrix.E₆_transpose E6_positive_definite E6Base E6Index K w*
      wordUnit A CartanMatrix.E₆_transpose E6_positive_definite E6Base E6Index K v*
      (wordUnit A CartanMatrix.E₆_transpose E6_positive_definite E6Base E6Index K w)⁻¹*
      (wordUnit A CartanMatrix.E₆_transpose E6_positive_definite E6Base E6Index K v)⁻¹∈
      diagonalNormalizer K := by
  have hlin : linearAction ((w++v)++inverseWord w)=linearAction v := by
    rw [linearAction_append,linearAction_append,linearAction_inverseWord,hc,
      mul_assoc,mul_inv_cancel,mul_one]
  have hh := same_action_word_ratio_mem K ((w++v)++inverseWord w) v hlin
  simpa only [wordUnit_append,wordUnit_inverseWord] using hh

def oppositionSimpleRatio (K : Type) [Field K] (a : Fin 4) :
    (Matrix GeckIndex GeckIndex K)ˣ :=
  relativeOpposition K*canonicalWord rawData K (orbitWord a)*(relativeOpposition K)⁻¹*
    (canonicalWord rawData K (orbitWord a))⁻¹

theorem opposition_simple_commutator_mem_diagonalNormalizer (K : Type) [Field K] (a : Fin 4) :
    oppositionSimpleRatio K a∈diagonalNormalizer K := by
  have h := commutator_mem_of_action_commute K oppositionWord (orbitWord a)
    (opposition_orbit_action_commute a)
  change relativeOpposition K*canonicalWord rawData K (orbitWord a)*(relativeOpposition K)⁻¹*
    (canonicalWord rawData K (orbitWord a))⁻¹∈diagonalNormalizer K
  simpa only [relativeOpposition,word_eq_canonicalWord] using h

end SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckOppositionSimpleRatio
