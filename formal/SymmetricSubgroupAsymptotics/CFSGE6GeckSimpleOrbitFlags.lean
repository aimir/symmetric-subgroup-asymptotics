import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckNonnegativeHeightFlag
import SymmetricSubgroupAsymptotics.CFSGGradedMatrixTriangularDegree
import SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckNormalizerEnvelope
import SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckFixedSimpleTests
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckWordLatticeSupport

/-! Four actual integral flags distinguish the four simple folded Weyl
representatives. The a-th grading is zero precisely on the a-th diagram
orbit. The upper envelope and that orbit's Weyl representative preserve
its weak flag; every other simple representative violates it. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical Matrix
namespace SymmetricSubgroupAsymptotics.CFSGE6GeckSimpleOrbitFlags
open CFSGTwistedE6GeckDiagramCovariance CFSGTwistedE6GeckNormalizerEnvelope
open CFSGTwistedE6WeylChamber CFSGTwistedE6RelativeWeylOrbits
open CFSGTwistedE6GeckFixedSimpleTests CFSGExceptionalNormTwoBases
open CFSGExceptionalCartanPositiveDefinite CFSGNormTwoRootPairing
open CFSGNormTwoGeckNonnegativeHeightFlag CFSGGradedMatrixTriangularDegree
open CFSGGradedMatrixSubgroups CFSGGradedMatrixTriangularUnits
open CFSGNormTwoGeckHeightSupport CFSGNormTwoGeckLatticeDegree
open CFSGNormTwoGeckWordLatticeSupport CFSGNormTwoGeckWeylWordDegree
open CFSGNormTwoCoordinateLatticeWord CFSGSignedCartanReflections
open CFSGSerreQuadraticWeylWord CFSGNormTwoGeckIntegralWord
local notation "A" => CartanMatrix.E₆
local notation "hs" => CartanMatrix.E₆_transpose
local notation "hp" => E6_positive_definite

private abbrev coordinate (i : Fin 6) : (Fin 6→ℤ)→ₗ[ℤ]ℤ := LinearMap.proj i

def orbitHeight (a : Fin 4) : (Fin 6→ℤ)→ₗ[ℤ]ℤ :=
  ![coordinate 1+coordinate 2+coordinate 3+coordinate 4,
    coordinate 0+coordinate 1+coordinate 3+coordinate 5,
    coordinate 0+coordinate 1+coordinate 2+coordinate 4+coordinate 5,
    coordinate 0+coordinate 2+coordinate 3+coordinate 4+coordinate 5] a

theorem orbitHeight_single (a : Fin 4) (i : Fin 6) :
    orbitHeight a (Pi.single i 1)=if i∈orbitWord a then 0 else 1 := by
  fin_cases a <;> fin_cases i <;>
    norm_num [orbitHeight,coordinate,orbitWord,Pi.single_apply,Fin.ext_iff]

theorem orbitHeight_simple (a : Fin 4) (i : Fin 6) :
    orbitHeight a (E6Index i : Roots A).val=if i∈orbitWord a then 0 else 1 := by
  change orbitHeight a (Pi.single i 1)=_
  exact orbitHeight_single a i

def orbitFlag (K : Type) [Field K] (a : Fin 4) : Subgroup (Matrix GeckIndex GeckIndex K)ˣ :=
  triangularUnits (fun j=> -weight A hs hp E6Base (orbitHeight a) j)

theorem envelope_le_orbitFlag (K : Type) [Field K] (a : Fin 4) :
    normalizerEnvelope K≤orbitFlag K a := by
  intro g hg
  obtain ⟨u,hu,d,hdD,hdiag,he⟩ := normalizer_envelope_factor K g hg
  have hU := positive_le_reverse_triangular A hs hp E6Base E6Index (orbitHeight a)
    (fun i=>by rw [orbitHeight_simple];split_ifs <;> omega) K hu
  have hD : d∈orbitFlag K a := by
    intro i j hij
    exact hdiag (by intro heq;subst j;exact (lt_irrefl _ hij))
  rw [he]
  exact (orbitFlag K a).mul_mem hU hD

theorem simple_weyl_mem_orbitFlag (K : Type) [Field K] (a : Fin 4) :
    canonicalWord rawData K (orbitWord a)∈orbitFlag K a := by
  have hpres := zero_degree_word_preserving A hs hp E6Base E6Index (orbitHeight a) K
    (orbitWord a) (fun i hi=>by rw [orbitHeight_simple,if_pos hi])
  exact ((triangular_inf_reverse_eq_preserving
    (weight A hs hp E6Base (orbitHeight a))).ge hpres).2

theorem orbit_action_test_neg (b : Fin 4) :
    linearAction (orbitWord b) (E6Index (testCoordinate b) : Roots A).val=
      -(E6Index (testCoordinate b) : Roots A).val := by
  have hm : ∀b : Fin 4,latticeWord A (orbitWord b)*ᵥ
      (Pi.single (testCoordinate b) (1:ℤ) : Fin 6→ℤ)=
      -(Pi.single (testCoordinate b) (1:ℤ) : Fin 6→ℤ) := by decide
  have hl := LinearMap.congr_fun (latticeWord_linear A CartanMatrix.E₆_diag hs hp
    CartanMatrix.E₆_off_diag_nonpos (orbitWord b))
      (Pi.single (testCoordinate b) (1:ℤ) : Fin 6→ℤ)
  change latticeWord A (orbitWord b)*ᵥ(Pi.single (testCoordinate b) (1:ℤ) : Fin 6→ℤ)=
    linearAction (orbitWord b) (Pi.single (testCoordinate b) (1:ℤ) : Fin 6→ℤ) at hl
  exact hl.symm.trans (hm b)

theorem other_simple_weyl_not_mem_orbitFlag (K : Type) [Field K]
    (a b : Fin 4) (hne : b≠a) :
    canonicalWord rawData K (orbitWord b)∉orbitFlag K a := by
  intro hflag
  have hmem : testCoordinate b∉orbitWord a := by
    revert hne
    fin_cases a <;> fin_cases b <;> decide
  have hsupp := word_lattice_support A hs hp E6Base E6Index K (orbitWord b)
  have hweight : (fun j=> -orbitHeight a (latticeWeight A hs hp E6Base j))=
      (fun j=> -weight A hs hp E6Base (orbitHeight a) j) := by
    funext j
    cases j <;> simp only [latticeWeight,weight,map_zero]
  have hh := degree_le_of_reverse_triangular (latticeWeight A hs hp E6Base)
    (orbitHeight a) (linearAction (orbitWord b))
      (wordUnit A hs hp E6Base E6Index K (orbitWord b)) hsupp
      (show Matrix.BlockTriangular
        (wordUnit A hs hp E6Base E6Index K (orbitWord b) : Matrix GeckIndex GeckIndex K)
        (fun j=> -orbitHeight a (latticeWeight A hs hp E6Base j)) from by
          rw [hweight]
          simpa only [word_eq_canonicalWord] using hflag)
      (Sum.inr (E6Index (testCoordinate b) : Roots A))
  change orbitHeight a (E6Index (testCoordinate b) : Roots A).val≤
    orbitHeight a (linearAction (orbitWord b) (E6Index (testCoordinate b) : Roots A).val) at hh
  rw [orbit_action_test_neg,map_neg,orbitHeight_simple,if_neg hmem] at hh
  omega

end SymmetricSubgroupAsymptotics.CFSGE6GeckSimpleOrbitFlags
