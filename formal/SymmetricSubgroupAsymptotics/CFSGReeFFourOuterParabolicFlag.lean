import SymmetricSubgroupAsymptotics.CFSGReeFFourMiddleParabolicFlag
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateLatticeWord

/-! The second proper relative parabolic candidate in the SAME original
fixed group. Its integer flag counts the three middle E6 coordinates;
the outer word preserves that flag and the middle word violates it. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical Matrix
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourOuterParabolicFlag
open CFSGTwistedE6GeckDiagramCovariance CFSGTwistedE6GeckNormalizerEnvelope
open CFSGTwistedE6WeylChamber CFSGReeFFourRelativeWeylRawWords
open CFSGReeFFourRelativePositiveSubgroups CFSGReeFFourRelativeSimpleWeyl
open CFSGReeFFourFixedPositiveFamilies CFSGReeFFourFixedBruhatCover
open CFSGReeFFourFixedModelEquivalence CFSGReeFFourFieldParameters
open CFSGNormTwoGeckNonnegativeHeightFlag CFSGGradedMatrixTriangularDegree
open CFSGGradedMatrixSubgroups CFSGGradedMatrixTriangularUnits
open CFSGNormTwoGeckHeightSupport CFSGNormTwoGeckLatticeDegree
open CFSGNormTwoGeckWordLatticeSupport CFSGNormTwoGeckWeylWordDegree
open CFSGNormTwoGeckWeylLatticeLinear CFSGNormTwoGeckIntegralWord
open CFSGNormTwoCoordinateLatticeWord CFSGSignedCartanReflections
open CFSGSerreQuadraticWeylWord CFSGNormTwoRootPairing
open CFSGExceptionalNormTwoBases CFSGExceptionalCartanPositiveDefinite
local notation "A" => CartanMatrix.E₆
local notation "hd" => CartanMatrix.E₆_diag
local notation "hs" => CartanMatrix.E₆_transpose
local notation "hp" => E6_positive_definite
local notation "ho" => CartanMatrix.E₆_off_diag_nonpos
local instance : DecidableEq (Roots A) := Classical.decEq _

private abbrev coordinate (i : Fin 6) : (Fin 6→ℤ)→ₗ[ℤ]ℤ := LinearMap.proj i

def insideHeight : (Fin 6→ℤ)→ₗ[ℤ]ℤ :=
  (coordinate 2+coordinate 3)+coordinate 4

private theorem inside_simple (i : Fin 6) :
    insideHeight (E6Index i : Roots A).val=if i=2∨i=3∨i=4 then 1 else 0 := by
  fin_cases i <;> rfl

def outerFlag (K : Type) [_root_.Field K] : Subgroup (Matrix GeckIndex GeckIndex K)ˣ :=
  triangularUnits (fun j=> -weight A hs hp E6Base insideHeight j)

theorem envelope_le_outerFlag (K : Type) [_root_.Field K] :
    normalizerEnvelope K≤outerFlag K := by
  intro g hg
  obtain ⟨u,hu,d,hdD,hdiag,he⟩ := normalizer_envelope_factor K g hg
  have hU := positive_le_reverse_triangular A hs hp E6Base E6Index insideHeight
    (fun i=>by rw [inside_simple];split_ifs <;> omega) K hu
  have hD : d∈outerFlag K := by
    intro i j hij
    exact hdiag (by intro heq;subst j;exact (lt_irrefl _ hij))
  rw [he]
  exact (outerFlag K).mul_mem hU hD

theorem outer_word_mem_flag (K : Type) [_root_.Field K] :
    wordUnit A hs hp E6Base E6Index K [0,5,1]∈outerFlag K := by
  have hz : ∀i∈([0,5,1] : List (Fin 6)),insideHeight (E6Index i : Roots A).val=0 := by
    intro i hi
    rw [inside_simple]
    fin_cases i <;> simp_all
  have hpres := zero_degree_word_preserving A hs hp E6Base E6Index insideHeight K [0,5,1] hz
  have ht := ((triangular_inf_reverse_eq_preserving
    (weight A hs hp E6Base insideHeight)).ge hpres).2
  simpa only [word_eq_canonicalWord] using ht

private theorem middle_action_test :
    linearAction [2,4,3,2,4,3] (E6Index 3 : Roots A).val=
      -(E6Index 3 : Roots A).val := by
  have h := LinearMap.congr_fun (latticeWord_linear A hd hs hp ho [2,4,3,2,4,3])
    (Pi.single 3 (1:ℤ) : Fin 6→ℤ)
  change latticeWord A [2,4,3,2,4,3]*ᵥ(Pi.single 3 (1:ℤ) : Fin 6→ℤ)=
    linearAction [2,4,3,2,4,3] (E6Index 3 : Roots A).val at h
  have hc : latticeWord A [2,4,3,2,4,3]*ᵥ(Pi.single 3 (1:ℤ) : Fin 6→ℤ)=
      -(Pi.single 3 (1:ℤ) : Fin 6→ℤ) := by decide
  exact h.symm.trans hc

theorem middle_word_not_mem_flag (K : Type) [_root_.Field K] :
    wordUnit A hs hp E6Base E6Index K [2,4,3,2,4,3]∉outerFlag K := by
  intro hflag
  have hsupp := word_lattice_support A hs hp E6Base E6Index K [2,4,3,2,4,3]
  have hweight : (fun j=> -insideHeight (latticeWeight A hs hp E6Base j))=
      (fun j=> -weight A hs hp E6Base insideHeight j) := by
    funext j
    cases j <;> simp only [latticeWeight,weight,map_zero]
  have hh := degree_le_of_reverse_triangular (latticeWeight A hs hp E6Base)
    insideHeight (linearAction [2,4,3,2,4,3])
      (wordUnit A hs hp E6Base E6Index K [2,4,3,2,4,3]) hsupp
      (show Matrix.BlockTriangular
        (wordUnit A hs hp E6Base E6Index K [2,4,3,2,4,3] : Matrix GeckIndex GeckIndex K)
        (fun j=> -insideHeight (latticeWeight A hs hp E6Base j)) from by
          rw [hweight]
          exact hflag)
      (Sum.inr (E6Index 3 : Roots A))
  change insideHeight (E6Index 3 : Roots A).val≤
    insideHeight (linearAction [2,4,3,2,4,3] (E6Index 3 : Roots A).val) at hh
  rw [middle_action_test,map_neg,inside_simple] at hh
  norm_num at hh

def fixedOuterFlag (m : ℕ) : Subgroup (originalModelFixed m) :=
  (outerFlag (Field m)).comap (fixedRawHom m)

def outerParabolic (m : ℕ) : Subgroup (originalModelFixed m) :=
  (fixedPositive m⊔fixedDiagonal m)⊔Subgroup.closure {outerFixedWeyl m}

theorem outerParabolic_le_flag (m : ℕ) : outerParabolic m≤fixedOuterFlag m := by
  apply sup_le
  · apply sup_le
    · intro u hu
      exact envelope_le_outerFlag (Field m) (positive_le_envelope (Field m) hu)
    · intro d hdD
      exact envelope_le_outerFlag (Field m) (diagonalNormalizer_le_envelope (Field m) hdD)
  · apply (Subgroup.closure_le _).mpr
    intro w hw
    have he : w=outerFixedWeyl m := Set.mem_singleton_iff.mp hw
    subst w
    change fixedRawHom m (outerFixedWeyl m)∈outerFlag (Field m)
    rw [fixedRawHom_apply]
    change CFSGFFourOriginalMiddleWords.rawHom (Field m) (outerRelativeWeyl m)∈_
    rw [rawHom_outerRelativeWeyl]
    exact outer_word_mem_flag (Field m)

theorem middleFixedWeyl_not_mem_outerParabolic (m : ℕ) :
    middleFixedWeyl m∉outerParabolic m := by
  intro hm
  have hflag := outerParabolic_le_flag m hm
  change CFSGFFourOriginalMiddleWords.rawHom (Field m) (middleRelativeWeyl m)∈outerFlag (Field m)
    at hflag
  rw [rawHom_middleRelativeWeyl] at hflag
  exact middle_word_not_mem_flag (Field m) hflag

theorem outerParabolic_ne_top (m : ℕ) : outerParabolic m≠⊤ := by
  intro htop
  exact middleFixedWeyl_not_mem_outerParabolic m (by rw [htop];exact Subgroup.mem_top _)

end SymmetricSubgroupAsymptotics.CFSGReeFFourOuterParabolicFlag
