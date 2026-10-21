import SymmetricSubgroupAsymptotics.BinaryPairLayerDenominatorCertificate
import SymmetricSubgroupAsymptotics.BinaryRegularEightNaturalRegistryRadicals
import SymmetricSubgroupAsymptotics.BinaryRegularEightNaturalRegistryComplete

set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
noncomputable section
open scoped BigOperators Classical
namespace SymmetricSubgroupAsymptotics.BinaryPairLayerHead8T3Kernel23Chunk1
open BinaryRegularEightNaturalRegistry

def sourceIndex : Fin 120 → Fin 47 := ![12,12,12,12,12,13,13,13,13,13,13,13,13,13,13,13,13,13,13,13,13,13,13,13,13,13,13,13,13,13,13,13,14,14,14,14,14,14,14,15,15,15,15,15,15,15,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,17,17,17,17,17,17,17,17,17,17,17,17,17,17,17,17,17,17,17,17,17,17,17,17,17,17,17,18,18,18,18,18,18,18,19,19,19,19,19,19,19,19,19,19,19,19,19]
def targetIndex : Fin 120 → Fin 47 := ![24,25,26,27,45,1,4,6,7,13,14,15,18,24,25,26,27,28,29,30,31,32,33,34,35,36,37,38,39,40,45,46,1,14,25,29,32,35,45,1,15,24,31,32,33,45,1,3,5,7,10,11,16,18,24,25,26,27,28,29,30,31,32,33,34,35,36,37,38,41,42,45,46,1,2,7,8,9,12,17,18,24,25,26,27,28,29,30,31,32,33,34,35,36,37,38,43,44,45,46,1,18,26,28,32,36,45,1,2,5,6,10,12,14,19,24,25,26,27,28]
def denominatorIndex : Fin 120 → Fin 47 := ![27,27,27,12,27,45,40,39,38,13,39,40,38,46,46,46,46,46,46,46,46,46,40,46,39,38,46,13,13,13,46,13,45,14,35,35,35,14,35,45,15,33,33,33,15,33,45,42,41,38,41,42,16,38,46,46,46,46,46,46,42,46,46,46,41,46,38,46,16,16,16,46,16,45,43,38,44,44,43,17,38,46,46,46,43,46,46,46,46,46,46,46,46,38,44,17,17,17,46,17,45,18,36,36,36,18,36,45,43,41,39,41,43,39,19,46,46,46,43,46]
def coefficientMask (p : Fin 120) (j : ℕ) : ℕ :=
  ((#[#[69,70,4,76,68],#[69,70,4,76,68],#[69,70,4,76,68],#[1,2,32,36],#[69,70,4,76,68],#[1,2,4,8,16,32,64],#[1,2,4],#[1,2,4],#[1,2,4],#[2,3],#[1,2,4],#[1,2,4],#[1,2,4],#[1,2,4,8],#[1,2,4,8],#[1,2,4,8],#[1,2,11,15],#[1,2,4,8],#[1,2,4,8],#[1,13,4,15],#[1,2,4,8],#[1,2,4,8],#[1,2,4],#[14,2,4,15],#[1,2,4],#[1,2,4],#[14,13,11,15],#[2,3],#[2,3],#[2,3],#[1,2,4,8],#[2,3],#[1,2,4,8,16,32,64],#[8,2,9,4],#[1,19,21,25,17],#[1,19,21,25,17],#[1,19,21,25,17],#[8,2,9,4],#[1,19,21,25,17],#[1,2,4,8,16,32,64],#[1,16,18,4],#[35,2,38,42,34],#[35,2,38,42,34],#[35,2,38,42,34],#[1,16,18,4],#[35,2,38,42,34],#[1,2,4,8,16,32,64],#[1,2,4],#[1,2,4],#[1,2,4],#[1,2,4],#[1,2,4],#[2,3],#[1,2,4],#[1,2,4,8],#[1,2,4,8],#[1,2,4,8],#[1,2,15,11],#[1,2,4,8],#[1,2,4,8],#[1,2,4],#[1,2,4,8],#[1,2,4,8],#[1,13,15,4],#[1,2,4],#[14,2,15,4],#[1,2,4],#[10,9,15,11],#[2,3],#[2,3],#[2,3],#[1,2,4,8],#[2,3],#[1,2,4,8,16,32,64],#[1,2,4],#[1,2,4],#[1,2,4],#[1,2,4],#[1,2,4],#[2,3],#[1,2,4],#[1,2,4,8],#[1,2,4,8],#[1,2,4,8],#[1,2,4],#[1,2,4,8],#[1,2,4,8],#[1,9,4,11],#[1,2,4,8],#[1,2,4,8],#[1,9,11,4],#[10,2,4,11],#[10,2,11,4],#[1,2,4],#[1,2,4],#[2,3],#[2,3],#[2,3],#[1,2,4,8],#[2,3],#[1,2,4,8,16,32,64],#[8,9,2,4],#[1,19,21,25,17],#[1,19,21,25,17],#[1,19,21,25,17],#[8,9,2,4],#[1,19,21,25,17],#[1,2,4,8,16,32,64],#[1,2,4],#[1,2,4],#[1,2,4],#[1,2,4],#[1,2,4],#[1,2,4],#[2,3],#[1,2,4,8],#[1,2,4,8],#[1,2,4,8],#[1,2,4],#[1,2,4,8]] : Array (Array ℕ))[p.val]!)[j]!
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

end SymmetricSubgroupAsymptotics.BinaryPairLayerHead8T3Kernel23Chunk1
