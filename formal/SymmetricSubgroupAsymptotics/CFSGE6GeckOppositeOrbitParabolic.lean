import SymmetricSubgroupAsymptotics.CFSGE6GeckFixedNegativeNormalizer
import SymmetricSubgroupAsymptotics.CFSGE6GeckOrbitRootIntersection
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateOppositeFunctionalFlag

/-! The actual negative fixed normalizer and the a-th folded Weyl word
preserve the forward orbit-excluded flag. The normalizer retains its
entire diagonal envelope; no generated-torus identification is used. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGE6GeckOppositeOrbitParabolic
open CFSGE6GeckFixedNegativeNormalizer CFSGE6GeckOrbitRootIntersection
open CFSGE6GeckSimpleOrbitFlags CFSGTwistedE6GeckDiagramCovariance
open CFSGTwistedE6GeckRelativeRootGenerated CFSGTwistedE6GeckPositiveTwist
open CFSGTwistedE6RelativeWeylOrbits CFSGExceptionalNormTwoBases
open CFSGExceptionalCartanPositiveDefinite CFSGExceptionalNormalizerWordIdentity
open CFSGSignedCartanReflections CFSGNormTwoGeckHeightSupport
open CFSGNormTwoGeckNonnegativeHeightFlag CFSGNormTwoGeckLatticeDegree
open CFSGGradedMatrixSubgroups CFSGGradedMatrixTriangularUnits
open CFSGNormTwoCoordinateOppositeFunctionalFlag CFSGSerreQuadraticWeylWord
local notation "A" => CartanMatrix.E₆
local notation "hd" => CartanMatrix.E₆_diag
local notation "hs" => CartanMatrix.E₆_transpose
local notation "hp" => E6_positive_definite
local notation "ho" => CartanMatrix.E₆_off_diag_nonpos

def negativeGeneratedNormalizer (K : Type) [Field K] (sigma : K≃+*K) :
    Subgroup (Matrix GeckIndex GeckIndex K)ˣ :=
  Subgroup.normalizer (signedFixed K sigma true : Set (Matrix GeckIndex GeckIndex K)ˣ) ⊓
    fixedRootGenerated K sigma

def oppositeOrbitParabolic (K : Type) [Field K] (sigma : K≃+*K) (a : Fin 4) :
    Subgroup (Matrix GeckIndex GeckIndex K)ˣ :=
  negativeGeneratedNormalizer K sigma ⊔
    Subgroup.closure {canonicalWord rawData K (orbitWord a)}

theorem fixed_negative_le_normalizer (K : Type) [Field K] (sigma : K≃+*K) :
    signedFixed K sigma true≤negativeGeneratedNormalizer K sigma :=
  le_inf (signedFixed K sigma true).le_normalizer (signedFixed_le_generated K sigma true)

theorem simple_weyl_mem_orbitLowerFlag (K : Type) [Field K] (a : Fin 4) :
    canonicalWord rawData K (orbitWord a)∈orbitLowerFlag K a := by
  have hpres := zero_degree_word_preserving A hs hp E6Base E6Index (orbitHeight a) K
    (orbitWord a) (fun i hi=>by rw [orbitHeight_simple,if_pos hi])
  have hw : (fun j=>orbitHeight a (latticeWeight A hs hp E6Base j))=
      weight A hs hp E6Base (orbitHeight a) := by
    funext j
    cases j <;> simp only [latticeWeight,weight,map_zero]
  change canonicalWord rawData K (orbitWord a)∈triangularUnits
    (fun j=>orbitHeight a (latticeWeight A hs hp E6Base j))
  rw [hw]
  exact ((triangular_inf_reverse_eq_preserving
    (weight A hs hp E6Base (orbitHeight a))).ge hpres).1

theorem negative_normalizer_le_orbitLowerFlag (K : Type) [Field K] [Finite K]
    (sigma : K≃+*K) (a : Fin 4) :
    negativeGeneratedNormalizer K sigma≤orbitLowerFlag K a := by
  have hflag : Subgroup.normalizer (Negative K : Set (Matrix GeckIndex GeckIndex K)ˣ) ⊓
      CFSGTwistedE6GeckSourceAction.MatrixGroup K≤orbitLowerFlag K a :=
    negative_normalizer_le_functional_flag A hd hs hp ho K E6Signs E6_signs_square
      E6_signs_cartan (E6_normalizer_word_identity K) (orbitHeight a)
        (fun i=>by
          change 0≤orbitHeight a (E6Index i : CFSGNormTwoRootPairing.Roots A).val
          rw [orbitHeight_simple]
          split_ifs <;> omega)
  exact (negative_normalizer_inter_generated_le K sigma).trans hflag

theorem oppositeOrbitParabolic_le_orbitLowerFlag (K : Type) [Field K] [Finite K]
    (sigma : K≃+*K) (a : Fin 4) :
    oppositeOrbitParabolic K sigma a≤orbitLowerFlag K a := by
  apply sup_le (negative_normalizer_le_orbitLowerFlag K sigma a)
  exact (Subgroup.closure_le _).mpr
    (Set.singleton_subset_iff.mpr (simple_weyl_mem_orbitLowerFlag K a))

theorem oppositeOrbitParabolic_le_generated (K : Type) [Field K]
    (sigma : K≃+*K) (a : Fin 4) :
    oppositeOrbitParabolic K sigma a≤fixedRootGenerated K sigma := by
  apply sup_le inf_le_right
  apply (Subgroup.closure_le _).mpr
  apply Set.singleton_subset_iff.mpr
  simpa only [CFSGNormTwoGeckIntegralWord.word_eq_canonicalWord,
    CFSGTwistedE6FixedWordClassification.expandRelative,List.append_nil] using
      relativeWord_mem_generated K sigma [a]

end SymmetricSubgroupAsymptotics.CFSGE6GeckOppositeOrbitParabolic
