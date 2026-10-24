import SymmetricSubgroupAsymptotics.CFSGE6GeckSimpleOrbitFlags
import SymmetricSubgroupAsymptotics.CFSGE6GeckMiddleRootSupport
import SymmetricSubgroupAsymptotics.CFSGReeFFourOuterInversionRoots
import SymmetricSubgroupAsymptotics.CFSGReeFFourRelativePositiveSubgroups
import SymmetricSubgroupAsymptotics.CFSGReeFFourFixedBruhatCover
import SymmetricSubgroupAsymptotics.CFSGReeFFourRelativeWeylRawWords

/-! A genuine proper middle parabolic candidate in the full original
exceptional-fixed group. The weak integer-height flag is preserved by
the upper envelope and middle Weyl word, and violated by the outer word.
No parabolic cell count, original simplicity, or derived identification
is assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical Matrix
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourMiddleParabolicFlag
open CFSGE6GeckMiddleRootSupport CFSGTwistedE6GeckDiagramCovariance
open CFSGTwistedE6GeckNormalizerEnvelope CFSGTwistedE6WeylChamber
open CFSGReeFFourOuterInversionRoots CFSGReeFFourRelativeWeylRawWords
open CFSGReeFFourRelativePositiveSubgroups CFSGReeFFourRelativeSimpleWeyl
open CFSGReeFFourFixedPositiveFamilies CFSGReeFFourFixedBruhatCover
open CFSGReeFFourFixedModelEquivalence CFSGReeFFourFieldParameters
open CFSGNormTwoGeckNonnegativeHeightFlag CFSGGradedMatrixTriangularDegree
open CFSGGradedMatrixSubgroups CFSGGradedMatrixTriangularUnits
open CFSGNormTwoGeckHeightSupport CFSGNormTwoGeckLatticeDegree
open CFSGNormTwoGeckWordLatticeSupport CFSGNormTwoGeckWeylWordDegree
open CFSGNormTwoGeckWeylLatticeLinear CFSGNormTwoGeckIntegralWord
open CFSGSerreQuadraticWeylWord CFSGNormTwoRootPairing
open CFSGExceptionalNormTwoBases CFSGExceptionalCartanPositiveDefinite
local notation "A" => CartanMatrix.E₆
local notation "hs" => CartanMatrix.E₆_transpose
local notation "hp" => E6_positive_definite
local instance : DecidableEq (Roots A) := Classical.decEq _

private theorem outside_simple (i : Fin 6) :
    outsideHeight (E6Index i : Roots A).val=if i=0∨i=1∨i=5 then 1 else 0 := by
  fin_cases i <;> rfl

def middleFlag (K : Type) [_root_.Field K] : Subgroup (Matrix GeckIndex GeckIndex K)ˣ :=
  triangularUnits (fun j=> -weight A hs hp E6Base outsideHeight j)

theorem envelope_le_middleFlag (K : Type) [_root_.Field K] :
    normalizerEnvelope K≤middleFlag K := by
  intro g hg
  obtain ⟨u,hu,d,hdD,hdiag,he⟩ := normalizer_envelope_factor K g hg
  have hU := positive_le_reverse_triangular A hs hp E6Base E6Index outsideHeight
    (fun i=>by rw [outside_simple];split_ifs <;> omega) K hu
  have hD : d∈middleFlag K := by
    intro i j hij
    exact hdiag (by intro heq;subst j;exact (lt_irrefl _ hij))
  rw [he]
  exact (middleFlag K).mul_mem hU hD

theorem middle_word_mem_flag (K : Type) [_root_.Field K] :
    wordUnit A hs hp E6Base E6Index K [2,4,3,2,4,3]∈middleFlag K := by
  have hz : ∀i∈([2,4,3,2,4,3] : List (Fin 6)),outsideHeight (E6Index i : Roots A).val=0 := by
    intro i hi
    rw [outside_simple]
    fin_cases i <;> simp_all
  have hpres := zero_degree_word_preserving A hs hp E6Base E6Index outsideHeight K
    [2,4,3,2,4,3] hz
  have ht := ((triangular_inf_reverse_eq_preserving
    (weight A hs hp E6Base outsideHeight)).ge hpres).2
  simpa only [word_eq_canonicalWord] using ht

private theorem outer_action_test :
    linearAction [0,5,1] (E6Index 0 : Roots A).val= -(E6Index 0 : Roots A).val := by
  calc
    _=(wordRoot A hs hp E6Base E6Index [0,5,1] (E6Index 0)).val :=
      wordLinear_root A hs hp E6Base E6Index [0,5,1] (E6Index 0)
    _=_ := outer_word_simple_val 0 (by decide)

theorem outer_word_not_mem_flag (K : Type) [_root_.Field K] :
    wordUnit A hs hp E6Base E6Index K [0,5,1]∉middleFlag K := by
  intro hflag
  have hsupp := word_lattice_support A hs hp E6Base E6Index K [0,5,1]
  have hweight : (fun j=> -outsideHeight (latticeWeight A hs hp E6Base j))=
      (fun j=> -weight A hs hp E6Base outsideHeight j) := by
    funext j
    cases j <;> simp only [latticeWeight,weight,map_zero]
  have hh := degree_le_of_reverse_triangular (latticeWeight A hs hp E6Base)
    outsideHeight (linearAction [0,5,1])
      (wordUnit A hs hp E6Base E6Index K [0,5,1]) hsupp
      (show Matrix.BlockTriangular
        (wordUnit A hs hp E6Base E6Index K [0,5,1] : Matrix GeckIndex GeckIndex K)
        (fun j=> -outsideHeight (latticeWeight A hs hp E6Base j)) from by
          rw [hweight]
          exact hflag)
      (Sum.inr (E6Index 0 : Roots A))
  change outsideHeight (E6Index 0 : Roots A).val≤
    outsideHeight (linearAction [0,5,1] (E6Index 0 : Roots A).val) at hh
  rw [outer_action_test,map_neg,outside_simple] at hh
  norm_num at hh

def fixedMiddleFlag (m : ℕ) : Subgroup (originalModelFixed m) :=
  (middleFlag (Field m)).comap (fixedRawHom m)

def middleParabolic (m : ℕ) : Subgroup (originalModelFixed m) :=
  (fixedPositive m⊔fixedDiagonal m)⊔Subgroup.closure {middleFixedWeyl m}

theorem middleParabolic_le_flag (m : ℕ) : middleParabolic m≤fixedMiddleFlag m := by
  apply sup_le
  · apply sup_le
    · intro u hu
      exact envelope_le_middleFlag (Field m)
        (positive_le_envelope (Field m) hu)
    · intro d hdD
      exact envelope_le_middleFlag (Field m)
        (diagonalNormalizer_le_envelope (Field m) hdD)
  · apply (Subgroup.closure_le _).mpr
    intro w hw
    have he : w=middleFixedWeyl m := Set.mem_singleton_iff.mp hw
    subst w
    change fixedRawHom m (middleFixedWeyl m)∈middleFlag (Field m)
    rw [fixedRawHom_apply]
    change CFSGFFourOriginalMiddleWords.rawHom (Field m) (middleRelativeWeyl m)∈_
    rw [rawHom_middleRelativeWeyl]
    exact middle_word_mem_flag (Field m)

theorem middleParabolic_ne_top (m : ℕ) : middleParabolic m≠⊤ := by
  intro htop
  have hg : outerFixedWeyl m∈middleParabolic m := by rw [htop];exact Subgroup.mem_top _
  have hflag := middleParabolic_le_flag m hg
  change CFSGFFourOriginalMiddleWords.rawHom (Field m) (outerRelativeWeyl m)∈middleFlag (Field m)
    at hflag
  rw [rawHom_outerRelativeWeyl] at hflag
  exact outer_word_not_mem_flag (Field m) hflag

end SymmetricSubgroupAsymptotics.CFSGReeFFourMiddleParabolicFlag
