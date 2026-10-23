import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckNonnegativeHeightFlag
import SymmetricSubgroupAsymptotics.CFSGGradedMatrixTriangularDegree
import SymmetricSubgroupAsymptotics.CFSGTrialityGeckNormalizerEnvelope
import SymmetricSubgroupAsymptotics.CFSGTrialityRelativeWordLanguage
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckWordLatticeSupport

/-! Two integral weak flags distinguish the actual outer-three and
middle-singleton triality Weyl words. This is a flag certificate for
the relative rank-two minimal-overgroup route, not a BN-pair premise. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical Matrix
namespace SymmetricSubgroupAsymptotics.CFSGTrialityGeckSimpleOrbitFlags
open CFSGTrialityD4NormTwo CFSGTrialityGeckDiagramCovariance
open CFSGTrialityGeckNormalizerEnvelope CFSGTrialityRelativeWordLanguage
open CFSGTrialityD4WordDiscriminant CFSGNormTwoRootPairing
open CFSGNormTwoGeckNonnegativeHeightFlag CFSGGradedMatrixTriangularDegree
open CFSGGradedMatrixSubgroups CFSGGradedMatrixTriangularUnits
open CFSGNormTwoGeckHeightSupport CFSGNormTwoGeckLatticeDegree
open CFSGNormTwoGeckWordLatticeSupport CFSGNormTwoGeckWeylWordDegree
open CFSGNormTwoCoordinateLatticeWord CFSGSignedCartanReflections
open CFSGSerreQuadraticWeylWord CFSGNormTwoGeckIntegralWord
local notation "A" => CartanMatrix.D 4
local notation "hs" => CartanMatrix.D_transpose 4
local notation "hp" => D4_positive_definite
local instance : DecidableEq (Roots A) := Classical.decEq _

def orbitWord (a : Bool) : List (Fin 4) := if a then [1] else [0,2,3]

theorem orbitWord_eq_expand (a : Bool) : orbitWord a = expandRelative [a] := by
  cases a <;> rfl

private abbrev coordinate (i : Fin 4) : (Fin 4 → ℤ) →ₗ[ℤ] ℤ := LinearMap.proj i

def orbitHeight (a : Bool) : (Fin 4 → ℤ) →ₗ[ℤ] ℤ :=
  if a then coordinate 0 + coordinate 2 + coordinate 3 else coordinate 1

theorem orbitHeight_single (a : Bool) (i : Fin 4) :
    orbitHeight a (Pi.single i 1) = if i ∈ orbitWord a then 0 else 1 := by
  cases a <;> fin_cases i <;>
    norm_num [orbitHeight,coordinate,orbitWord,Pi.single_apply,Fin.ext_iff]

theorem orbitHeight_simple (a : Bool) (i : Fin 4) :
    orbitHeight a (Index i : Roots A).val = if i ∈ orbitWord a then 0 else 1 := by
  change orbitHeight a (Pi.single i 1) = _
  exact orbitHeight_single a i

def orbitFlag (K : Type) [Field K] (a : Bool) : Subgroup (Matrix GeckIndex GeckIndex K)ˣ :=
  triangularUnits (fun j => -weight A hs hp Base (orbitHeight a) j)

theorem envelope_le_orbitFlag (K : Type) [Field K] (a : Bool) :
    normalizerEnvelope K ≤ orbitFlag K a := by
  intro g hg
  obtain ⟨u,hu,d,hdD,hdiag,he⟩ := normalizer_envelope_factor K g hg
  have hU := positive_le_reverse_triangular A hs hp Base Index (orbitHeight a)
    (fun i => by rw [orbitHeight_simple]; split_ifs <;> omega) K hu
  have hD : d ∈ orbitFlag K a := by
    intro i j hij
    exact hdiag (by intro heq; subst j; exact (lt_irrefl _ hij))
  rw [he]
  exact (orbitFlag K a).mul_mem hU hD

theorem simple_weyl_mem_orbitFlag (K : Type) [Field K] (a : Bool) :
    canonicalWord rawData K (orbitWord a) ∈ orbitFlag K a := by
  have hpres := zero_degree_word_preserving A hs hp Base Index (orbitHeight a) K
    (orbitWord a) (fun i hi => by rw [orbitHeight_simple,if_pos hi])
  exact ((triangular_inf_reverse_eq_preserving
    (weight A hs hp Base (orbitHeight a))).ge hpres).2

def testCoordinate (a : Bool) : Fin 4 := if a then 1 else 0

theorem orbit_action_test_neg (b : Bool) :
    linearAction (orbitWord b) (Index (testCoordinate b) : Roots A).val =
      -(Index (testCoordinate b) : Roots A).val := by
  have hm : ∀ b : Bool, latticeWord A (orbitWord b) *ᵥ
      (Pi.single (testCoordinate b) (1 : ℤ) : Fin 4 → ℤ) =
      -(Pi.single (testCoordinate b) (1 : ℤ) : Fin 4 → ℤ) := by
    intro b
    cases b <;> decide
  have hl := LinearMap.congr_fun (latticeWord_linear A (CartanMatrix.D_diag 4) hs hp
    (CartanMatrix.D_off_diag_nonpos 4) (orbitWord b))
      (Pi.single (testCoordinate b) (1 : ℤ) : Fin 4 → ℤ)
  change latticeWord A (orbitWord b) *ᵥ (Pi.single (testCoordinate b) (1 : ℤ) : Fin 4 → ℤ) =
    linearAction (orbitWord b) (Pi.single (testCoordinate b) (1 : ℤ) : Fin 4 → ℤ) at hl
  exact hl.symm.trans (hm b)

theorem other_simple_weyl_not_mem_orbitFlag (K : Type) [Field K]
    (a b : Bool) (hne : b ≠ a) :
    canonicalWord rawData K (orbitWord b) ∉ orbitFlag K a := by
  intro hflag
  have hmem : testCoordinate b ∉ orbitWord a := by
    cases a <;> cases b <;> norm_num [testCoordinate,orbitWord,Fin.ext_iff] at *
  have hsupp := word_lattice_support A hs hp Base Index K (orbitWord b)
  have hweight : (fun j => -orbitHeight a (latticeWeight A hs hp Base j)) =
      (fun j => -weight A hs hp Base (orbitHeight a) j) := by
    funext j
    cases j <;> simp only [latticeWeight,weight,map_zero]
  have hh := degree_le_of_reverse_triangular (latticeWeight A hs hp Base)
    (orbitHeight a) (linearAction (orbitWord b))
      (wordUnit A hs hp Base Index K (orbitWord b)) hsupp
      (show Matrix.BlockTriangular
        (wordUnit A hs hp Base Index K (orbitWord b) : Matrix GeckIndex GeckIndex K)
        (fun j => -orbitHeight a (latticeWeight A hs hp Base j)) from by
          rw [hweight]
          simpa only [word_eq_canonicalWord] using hflag)
      (Sum.inr (Index (testCoordinate b) : Roots A))
  change orbitHeight a (Index (testCoordinate b) : Roots A).val ≤
    orbitHeight a (linearAction (orbitWord b) (Index (testCoordinate b) : Roots A).val) at hh
  rw [orbit_action_test_neg,map_neg,orbitHeight_simple,if_neg hmem] at hh
  omega

end SymmetricSubgroupAsymptotics.CFSGTrialityGeckSimpleOrbitFlags
