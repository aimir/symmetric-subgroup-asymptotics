import SymmetricSubgroupAsymptotics.CFSGReeFFourShortPairedWeylMenu
import SymmetricSubgroupAsymptotics.CFSGReeFFourOuterParabolicFlag

/-! A bounded weak-flag test for the sixteen retained word actions.
The outer parabolic admits only the identity and outer reflection
among these actions. No source-word equality is inferred here. -/
set_option autoImplicit false
set_option Elab.async false
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourOuterParabolicWordMenu
open CFSGReeFFourShortPairedWeylMenu CFSGReeFFourFixedWordClassification
open CFSGTwistedE6FixedWordClassification CFSGSignedCartanReflections
open CFSGNormTwoCoordinateLatticeWord

def middleSum (v : Fin 6→ℤ) : ℤ := v 2+v 3+v 4

theorem short_menu_outer_flag_test : ∀i : Fin 16,i=0∨i=1∨∃j : Fin 6,
    middleSum (latticeWord CartanMatrix.E₆ (expandRelative (expandPaired (shortWord i)))*ᵥ
      (Pi.single j (1:ℤ) : Fin 6→ℤ)) < middleSum (Pi.single j (1:ℤ) : Fin 6→ℤ) := by
  unfold middleSum
  decide +kernel

noncomputable section
open scoped Classical Matrix
open CFSGReeFFourOuterParabolicFlag CFSGTwistedE6GeckDiagramCovariance
open CFSGTwistedE6WeylChamber CFSGNormTwoGeckWordLatticeSupport
open CFSGNormTwoGeckLatticeDegree CFSGNormTwoGeckWeylLatticeLinear
open CFSGNormTwoGeckWeylWordDegree CFSGNormTwoGeckIntegralWord
open CFSGGradedMatrixTriangularDegree CFSGNormTwoRootPairing
open CFSGExceptionalNormTwoBases CFSGExceptionalCartanPositiveDefinite
local notation "A" => CartanMatrix.E₆
local notation "hd" => CartanMatrix.E₆_diag
local notation "hs" => CartanMatrix.E₆_transpose
local notation "hp" => E6_positive_definite
local notation "ho" => CartanMatrix.E₆_off_diag_nonpos
local instance : DecidableEq (Roots A) := Classical.decEq _

private theorem column_degree_le (K : Type) [_root_.Field K] (w : List (Fin 6))
    (hw : wordUnit A hs hp E6Base E6Index K w∈outerFlag K) (j : Fin 6) :
    middleSum (Pi.single j (1:ℤ) : Fin 6→ℤ)≤
      middleSum (latticeWord A w*ᵥ(Pi.single j (1:ℤ) : Fin 6→ℤ)) := by
  have hweight : (fun k=> -insideHeight (latticeWeight A hs hp E6Base k))=
      (fun k=> -CFSGNormTwoGeckHeightSupport.weight A hs hp E6Base insideHeight k) := by
    funext k
    cases k <;> simp only [latticeWeight,CFSGNormTwoGeckHeightSupport.weight,map_zero]
  have h := degree_le_of_reverse_triangular (latticeWeight A hs hp E6Base)
    insideHeight (linearAction w) (wordUnit A hs hp E6Base E6Index K w)
    (word_lattice_support A hs hp E6Base E6Index K w)
    (show Matrix.BlockTriangular
      (wordUnit A hs hp E6Base E6Index K w : Matrix GeckIndex GeckIndex K)
      (fun k=> -insideHeight (latticeWeight A hs hp E6Base k)) from by
        rw [hweight]
        exact hw) (Sum.inr (E6Index j : Roots A))
  change insideHeight (Pi.single j (1:ℤ) : Fin 6→ℤ)≤
    insideHeight (linearAction w (Pi.single j (1:ℤ) : Fin 6→ℤ)) at h
  have hc := LinearMap.congr_fun (latticeWord_linear A hd hs hp ho w)
    (Pi.single j (1:ℤ) : Fin 6→ℤ)
  change latticeWord A w*ᵥ(Pi.single j (1:ℤ) : Fin 6→ℤ)=
    linearAction w (Pi.single j (1:ℤ) : Fin 6→ℤ) at hc
  exact h.trans_eq (congrArg insideHeight hc.symm)

theorem short_word_mem_outerFlag_only (K : Type) [_root_.Field K] (i : Fin 16)
    (hi : wordUnit A hs hp E6Base E6Index K
      (expandRelative (expandPaired (shortWord i)))∈outerFlag K) : i=0∨i=1 := by
  rcases short_menu_outer_flag_test i with h0|h1|⟨j,hj⟩
  · exact Or.inl h0
  · exact Or.inr h1
  · exact False.elim (not_lt_of_ge (column_degree_le K _ hi j) hj)

end
end SymmetricSubgroupAsymptotics.CFSGReeFFourOuterParabolicWordMenu
