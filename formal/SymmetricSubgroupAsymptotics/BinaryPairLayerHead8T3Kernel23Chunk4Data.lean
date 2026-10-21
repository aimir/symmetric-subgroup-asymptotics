import SymmetricSubgroupAsymptotics.BinaryPairLayerDenominatorCertificate
import SymmetricSubgroupAsymptotics.BinaryRegularEightNaturalRegistryRadicals
import SymmetricSubgroupAsymptotics.BinaryRegularEightNaturalRegistryComplete

set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
noncomputable section
open scoped BigOperators Classical
namespace SymmetricSubgroupAsymptotics.BinaryPairLayerHead8T3Kernel23Chunk4
open BinaryRegularEightNaturalRegistry

def sourceIndex : Fin 120 → Fin 47 := ![39,39,39,39,40,40,40,40,40,40,40,40,40,40,40,40,40,40,40,40,40,40,40,40,41,41,41,41,41,41,41,41,41,41,41,41,41,41,41,41,41,41,41,41,42,42,42,42,42,42,42,42,42,42,42,42,42,42,42,42,42,42,42,42,43,43,43,43,43,43,43,43,43,43,43,43,43,43,43,43,43,43,43,43,44,44,44,44,44,44,44,44,44,44,44,44,44,44,44,44,44,44,44,44,45,45,46,46,46,46,46,46,46,46,46,46,46,46,46,46]
def targetIndex : Fin 120 → Fin 47 := ![37,39,45,46,1,4,15,24,25,26,27,28,29,30,31,32,33,34,35,36,37,40,45,46,1,5,10,24,25,26,27,28,29,30,31,32,33,34,35,36,37,41,45,46,1,3,11,24,25,26,27,28,29,30,31,32,33,34,35,36,37,42,45,46,1,2,12,24,25,26,27,28,29,30,31,32,33,34,35,36,37,43,45,46,1,8,9,24,25,26,27,28,29,30,31,32,33,34,35,36,37,44,45,46,1,45,1,24,25,26,27,28,29,30,31,32,33,34,35,36]
def denominatorIndex : Fin 120 → Fin 47 := ![46,39,46,39,45,40,40,46,46,46,46,46,46,46,46,46,40,46,46,46,46,40,46,40,45,41,41,46,46,46,46,46,46,46,46,46,46,41,46,46,46,41,46,41,45,42,42,46,46,46,46,46,46,42,46,46,46,46,46,46,46,42,46,42,45,43,43,46,46,46,43,46,46,46,46,46,46,46,46,46,46,43,46,43,45,44,44,46,46,46,46,46,46,46,46,46,46,46,46,46,44,44,46,44,45,45,45,46,46,46,46,46,46,46,46,46,46,46,46,46]
def coefficientMask (p : Fin 120) (j : ℕ) : ℕ :=
  ((#[#[19,16,22,18],#[2,4,7],#[1,2,4,8],#[2,4,7],#[1,2,4,8,16,32,64],#[1,2,4],#[1,2,4],#[1,2,4,8],#[1,2,4,8],#[1,2,4,8],#[1,2,18,22],#[1,2,4,8],#[1,2,4,8],#[1,20,4,22],#[1,2,4,8],#[1,2,4,8],#[1,2,4],#[8,2,4,9],#[8,2,9,4],#[8,9,2,4],#[8,11,13,9],#[2,4,7],#[1,2,4,8],#[2,4,7],#[1,2,4,8,16,32,64],#[1,2,4],#[1,2,4],#[1,2,4,8],#[1,2,4,8],#[1,2,4,8],#[1,2,13,9],#[1,2,4,8],#[1,2,4,8],#[1,11,4,9],#[1,2,4,8],#[1,2,4,8],#[1,16,18,4],#[1,2,4],#[12,2,13,4],#[12,13,2,4],#[19,16,22,18],#[2,4,7],#[1,2,4,8],#[2,4,7],#[1,2,4,8,16,32,64],#[1,2,4],#[1,2,4],#[1,2,4,8],#[1,2,4,8],#[1,2,4,8],#[1,2,22,18],#[1,2,4,8],#[1,2,4,8],#[1,2,4],#[1,2,4,8],#[1,2,4,8],#[1,20,22,4],#[8,2,4,9],#[8,2,9,4],#[8,9,2,4],#[8,11,13,9],#[2,4,7],#[1,2,4,8],#[2,4,7],#[1,2,4,8,16,32,64],#[1,2,4],#[1,2,4],#[1,2,4,8],#[1,2,4,8],#[1,2,4,8],#[1,2,4],#[1,2,4,8],#[1,2,4,8],#[1,16,4,18],#[1,2,4,8],#[1,2,4,8],#[1,16,18,4],#[8,2,4,9],#[8,2,9,4],#[8,9,2,4],#[8,11,13,9],#[2,4,7],#[1,2,4,8],#[2,4,7],#[1,2,4,8,16,32,64],#[1,2,4],#[1,2,4],#[1,2,4,8],#[1,2,4,8],#[1,2,4,8],#[1,2,13,9],#[1,2,4,8],#[1,2,4,8],#[1,11,4,9],#[1,2,4,8],#[1,2,4,8],#[1,20,22,4],#[19,2,4,18],#[12,2,13,4],#[12,13,2,4],#[1,2,4],#[2,4,7],#[1,2,4,8],#[2,4,7],#[1,2,4,8,16,32,64],#[16,32,55,128,153,170,187],#[1,2,4,8,16,32,64],#[1,2,4,8],#[1,2,4,8],#[1,2,4,8],#[1,2,32,36],#[1,2,4,8],#[1,2,4,8],#[1,16,4,18],#[1,2,4,8],#[1,2,4,8],#[1,16,18,4],#[8,2,4,9],#[8,2,9,4],#[8,9,2,4]] : Array (Array ℕ))[p.val]!)[j]!
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

end SymmetricSubgroupAsymptotics.BinaryPairLayerHead8T3Kernel23Chunk4
