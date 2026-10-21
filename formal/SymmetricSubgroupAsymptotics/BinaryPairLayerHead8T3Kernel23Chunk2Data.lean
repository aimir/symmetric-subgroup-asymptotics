import SymmetricSubgroupAsymptotics.BinaryPairLayerDenominatorCertificate
import SymmetricSubgroupAsymptotics.BinaryRegularEightNaturalRegistryRadicals
import SymmetricSubgroupAsymptotics.BinaryRegularEightNaturalRegistryComplete

set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
noncomputable section
open scoped BigOperators Classical
namespace SymmetricSubgroupAsymptotics.BinaryPairLayerHead8T3Kernel23Chunk2
open BinaryRegularEightNaturalRegistry

def sourceIndex : Fin 120 → Fin 47 := ![19,19,19,19,19,19,19,19,19,19,19,19,19,19,20,20,20,20,20,20,20,20,20,20,20,20,20,20,20,20,20,20,20,20,20,20,20,20,20,20,20,21,21,21,21,21,21,21,21,21,21,21,21,21,21,21,21,21,21,21,21,21,21,21,21,21,21,21,22,22,22,22,22,22,22,22,22,22,22,22,22,22,22,22,22,22,22,22,22,22,22,22,22,22,22,23,23,23,23,23,23,23,23,23,23,23,23,23,23,23,23,23,23,23,23,23,23,23,23,23]
def targetIndex : Fin 120 → Fin 47 := ![29,30,31,32,33,34,35,36,37,39,41,43,45,46,1,3,6,8,9,11,14,20,24,25,26,27,28,29,30,31,32,33,34,35,36,37,39,42,44,45,46,1,4,5,8,9,10,15,21,24,25,26,27,28,29,30,31,32,33,34,35,36,37,40,41,44,45,46,1,2,3,4,11,12,15,22,24,25,26,27,28,29,30,31,32,33,34,35,36,37,40,42,43,45,46,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25]
def denominatorIndex : Fin 120 → Fin 47 := ![46,46,46,46,46,41,39,46,46,19,19,19,46,19,45,42,39,44,44,42,39,20,46,46,46,46,46,46,42,46,46,46,46,39,46,44,20,20,20,46,20,45,40,41,44,44,41,40,21,46,46,46,46,46,46,46,46,46,40,41,46,46,44,21,21,21,46,21,45,43,42,40,42,43,40,22,46,46,46,43,46,46,42,46,46,40,46,46,46,46,22,22,22,46,22,45,43,42,40,41,39,38,44,44,41,42,43,23,39,40,23,23,38,23,23,23,23,23,46,46]
def coefficientMask (p : Fin 120) (j : ℕ) : ℕ :=
  ((#[#[1,2,4,8],#[1,15,4,13],#[1,2,4,8],#[1,2,4,8],#[1,15,13,4],#[1,2,4],#[1,2,4],#[14,15,2,4],#[12,15,9,13],#[2,3],#[2,3],#[2,3],#[1,2,4,8],#[2,3],#[1,2,4,8,16,32,64],#[1,2,4],#[1,2,4],#[1,2,4],#[1,2,4],#[1,2,4],#[1,2,4],#[2,3],#[1,2,4,8],#[1,2,4,8],#[1,2,4,8],#[1,2,9,13],#[1,2,4,8],#[1,2,4,8],#[1,2,4],#[1,2,4,8],#[1,2,4,8],#[1,11,9,4],#[12,2,4,13],#[1,2,4],#[10,11,2,4],#[1,2,4],#[2,3],#[2,3],#[2,3],#[1,2,4,8],#[2,3],#[1,2,4,8,16,32,64],#[1,2,4],#[1,2,4],#[1,2,4],#[1,2,4],#[1,2,4],#[1,2,4],#[2,3],#[1,2,4,8],#[1,2,4,8],#[1,2,4,8],#[1,2,13,9],#[1,2,4,8],#[1,2,4,8],#[1,11,4,9],#[1,2,4,8],#[1,2,4,8],#[1,2,4],#[1,2,4],#[12,2,13,4],#[12,13,2,4],#[1,2,4],#[2,3],#[2,3],#[2,3],#[1,2,4,8],#[2,3],#[1,2,4,8,16,32,64],#[1,2,4],#[1,2,4],#[1,2,4],#[1,2,4],#[1,2,4],#[1,2,4],#[2,3],#[1,2,4,8],#[1,2,4,8],#[1,2,4,8],#[1,2,4],#[1,2,4,8],#[1,2,4,8],#[1,2,4],#[1,2,4,8],#[1,2,4,8],#[1,2,4],#[8,2,4,9],#[8,2,9,4],#[8,9,2,4],#[8,11,13,9],#[2,3],#[2,3],#[2,3],#[1,2,4,8],#[2,3],#[1,2,4,8,16,32,64],#[1,2,4],#[1,2,4],#[1,2,4],#[1,2,4],#[1,2,4],#[1,2,4],#[1,2,4],#[1,2,4],#[1,2,4],#[1,2,4],#[1,2,4],#[1],#[1,2,4],#[1,2,4],#[1],#[1],#[1,2,4],#[1],#[1],#[1],#[1],#[1],#[1,2,4,8],#[1,2,4,8]] : Array (Array ℕ))[p.val]!)[j]!
def radicalCoefficient (p : Fin 120) (j : Fin (charts (denominatorIndex p)).1)
    (i : Fin (radicalCharts (targetIndex p)).1) : ZMod 2 :=
  if (coefficientMask p j).testBit i.val then 1 else 0
def productCoefficient (p : Fin 120) (j : Fin (charts (denominatorIndex p)).1)
    (i : Fin (charts 23).1) (k : Fin (charts (sourceIndex p)).1) : ZMod 2 :=
  if (coefficientMask p j).testBit
    ((radicalCharts (targetIndex p)).1 + i.val * (charts (sourceIndex p)).1 + k.val) then 1 else 0
private theorem denominator_basis_mem : ∀ p j,
    (charts (denominatorIndex p)).2.inclusion (Pi.single j 1) ∈
      (states (targetIndex p)).toSubmodule := by
  simp only [states_space]
  decide +kernel
private theorem denominator_basis_eq : ∀ p j,
    (charts (denominatorIndex p)).2.inclusion (Pi.single j 1) =
      (∑ i, radicalCoefficient p j i • (radicalCharts (targetIndex p)).2.inclusion (Pi.single i 1)) +
        ∑ i, ∑ k, productCoefficient p j i k •
          ((charts 23).2.inclusion (Pi.single i 1) *
            (charts (sourceIndex p)).2.inclusion (Pi.single k 1)) := by
  decide +kernel

def certificate (p : Fin 120) : BinaryPairLayerDenominatorCertificate rho
    (states (targetIndex p)) (charts 23).2 (charts (sourceIndex p)).2
      (radicalCharts (targetIndex p)).2 (charts (denominatorIndex p)).2 where
  space_le_state := (charts (denominatorIndex p)).2.le_of_basis_mem _ (denominator_basis_mem p)
  radicalCoefficient := radicalCoefficient p
  productCoefficient := productCoefficient p
  basis_eq := denominator_basis_eq p

private theorem scalar_bound : ∀ p : Fin 120,
    headCeiling (sourceIndex p) + (charts (targetIndex p)).1 ≤
      (charts (denominatorIndex p)).1 + 6 := by decide +kernel

theorem finite_pair_bound (p : Fin 120)
    (hproduct : binaryCoordinateProductSpan (charts 23).2.space
      (states (sourceIndex p)).toSubmodule ≤ (states (targetIndex p)).toSubmodule) :
    Module.finrank (ZMod 2) (states (sourceIndex p)).toRepresentation.Coinvariants +
      Module.finrank (ZMod 2) ((states (targetIndex p)).toSubmodule ⧸
        ((binaryCoordinateProductSpan (charts 23).2.space
          (states (sourceIndex p)).toSubmodule).comap (states (targetIndex p)).toSubmodule.subtype ⊔
            Representation.Coinvariants.ker (states (targetIndex p)).toRepresentation)) ≤ 6 := by
  let D := (binaryCoordinateProductSpan (charts 23).2.space
    (states (sourceIndex p)).toSubmodule).comap (states (targetIndex p)).toSubmodule.subtype ⊔
      Representation.Coinvariants.ker (states (targetIndex p)).toRepresentation
  have hin := (certificate p).submoduleOf_le_product_radical hproduct
    (coinvariantsKer_map_eq_radical (targetIndex p)).symm
  have hdim : (charts (denominatorIndex p)).1 ≤ Module.finrank (ZMod 2) D := by
    rw [← (charts (denominatorIndex p)).2.submoduleOf_finrank
      (states (targetIndex p)).toSubmodule (certificate p).space_le_state]
    exact Submodule.finrank_mono hin
  have hquot := D.finrank_quotient_add_finrank
  have hL : Module.finrank (ZMod 2) (states (targetIndex p)).toSubmodule =
      (charts (targetIndex p)).1 := by
    rw [states_space]
    exact (charts (targetIndex p)).2.finrank
  have hS := coinvariants_finrank_le (sourceIndex p)
  have hnum := scalar_bound p
  change Module.finrank (ZMod 2) (states (sourceIndex p)).toRepresentation.Coinvariants +
    Module.finrank (ZMod 2) ((states (targetIndex p)).toSubmodule ⧸ D) ≤ 6
  omega

def compatible (i j : Fin 47) : Prop := ∀ a : Fin (charts 23).1,
  ∀ b : Fin (charts i).1,
    (charts 23).2.inclusion (Pi.single a 1) * (charts i).2.inclusion (Pi.single b 1) ∈
      (charts j).2.space

theorem wide_indices : ∀ p : Fin 120,
    (charts (denominatorIndex p)).1 + 6 ≤
      headCeiling (sourceIndex p) + (charts (targetIndex p)).1 →
    (sourceIndex p = 46 ∧ targetIndex p = 45) := by decide +kernel

/-- The sparse denominator chart bounds the actual quotient. -/
theorem denominator_dimension_le (p : Fin 120)
    (hproduct : binaryCoordinateProductSpan (charts 23).2.space
      (states (sourceIndex p)).toSubmodule ≤ (states (targetIndex p)).toSubmodule) :
    (charts (denominatorIndex p)).1 +
      Module.finrank (ZMod 2) ((states (targetIndex p)).toSubmodule ⧸
        ((binaryCoordinateProductSpan (charts 23).2.space
          (states (sourceIndex p)).toSubmodule).comap (states (targetIndex p)).toSubmodule.subtype ⊔
            Representation.Coinvariants.ker (states (targetIndex p)).toRepresentation)) ≤
      (charts (targetIndex p)).1 := by
  let D := (binaryCoordinateProductSpan (charts 23).2.space
    (states (sourceIndex p)).toSubmodule).comap (states (targetIndex p)).toSubmodule.subtype ⊔
      Representation.Coinvariants.ker (states (targetIndex p)).toRepresentation
  have hin := (certificate p).submoduleOf_le_product_radical hproduct
    (coinvariantsKer_map_eq_radical (targetIndex p)).symm
  have hdim : (charts (denominatorIndex p)).1 ≤ Module.finrank (ZMod 2) D := by
    rw [← (charts (denominatorIndex p)).2.submoduleOf_finrank
      (states (targetIndex p)).toSubmodule (certificate p).space_le_state]
    exact Submodule.finrank_mono hin
  have hquot := D.finrank_quotient_add_finrank
  have hL : Module.finrank (ZMod 2) (states (targetIndex p)).toSubmodule =
      (charts (targetIndex p)).1 := by
    rw [states_space]
    exact (charts (targetIndex p)).2.finrank
  change (charts (denominatorIndex p)).1 +
    Module.finrank (ZMod 2) ((states (targetIndex p)).toSubmodule ⧸ D) ≤
      (charts (targetIndex p)).1
  omega

end SymmetricSubgroupAsymptotics.BinaryPairLayerHead8T3Kernel23Chunk2
