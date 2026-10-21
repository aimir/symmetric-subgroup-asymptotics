import SymmetricSubgroupAsymptotics.BinaryPairLayerDenominatorCertificate
import SymmetricSubgroupAsymptotics.BinaryHeisenbergEightNaturalHeads
import SymmetricSubgroupAsymptotics.BinaryHeisenbergEightNaturalCarrySpaces

set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
noncomputable section
open scoped BigOperators Classical
namespace SymmetricSubgroupAsymptotics.BinaryPairLayerHead8T22Kernel14
open BinaryHeisenbergEightNaturalHeads

def sourceIndex : Fin 71 → Fin 15 := ![0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,2,3,3,3,3,3,3,3,4,5,6,6,6,6,6,6,6,7,7,8,8,9,9,9,9,9,9,9,10,10,10,10,10,10,10,11,11,11,11,11,11,11,11,11,11,12,13,13,14,14,14,14,14,14,14]
def targetIndex : Fin 71 → Fin 15 := ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,1,1,1,2,3,4,5,12,13,1,1,1,2,3,4,5,12,13,1,12,1,12,1,2,3,4,5,12,13,1,2,3,4,5,12,13,1,2,3,4,5,7,8,12,13,14,1,1,12,1,2,3,4,5,12,13]
def denominatorIndex : Fin 71 → Fin 15 := ![0,12,13,14,13,13,11,14,14,11,11,0,13,14,11,1,1,12,13,3,13,13,13,3,1,1,12,13,3,13,13,13,3,12,12,12,12,12,13,3,13,13,13,3,12,13,3,13,13,13,3,12,13,14,13,13,14,14,13,14,14,1,12,12,12,13,3,13,13,13,3]
def coefficientMask (p : Fin 71) (j : ℕ) : ℕ :=
  ((#[#[],#[1,2,4,8,16,32,64],#[1,2,4,8,16],#[1,2,4],#[1,2,4,8,16],#[1,2,4,8,16],#[1],#[1,2,4],#[1,2,4],#[1],#[1],#[],#[1,2,4,8,16],#[1,2,4],#[1],#[128,131,133,137,145,161,193,129],#[16387,16384,16390,16394,16402,16418,16450,16386],#[1,2,4,8,16,32,64],#[1,2,4,8,16],#[8,11,13,9],#[1,2,4,8,16],#[1,2,4,8,16],#[1,2,4,8,16],#[8,11,13,9],#[321,322,324,328,336,352,256,320],#[257,258,260,264,272,288,320,256],#[1,2,4,8,16,32,64],#[1,2,4,8,16],#[8,11,13,9],#[1,2,4,8,16],#[1,2,4,8,16],#[1,2,4,8,16],#[8,11,13,9],#[1,2,4,8,16,32,64],#[1,1088,1094,1050,1042,64,80],#[1,2,4,8,16,32,64],#[1,1088,1094,1034,1026,80,64],#[1,2,4,8,16,32,64],#[1,2,4,8,16],#[8,11,13,9],#[1,2,4,8,16],#[1,2,4,8,16],#[1,2,4,8,16],#[8,11,13,9],#[1,2,4,8,16,32,64],#[1,2,4,8,16],#[33,34,36,32],#[1,2,4,8,16],#[1,2,4,8,16],#[1,2,4,8,16],#[33,34,36,32],#[1,2,4,8,16,32,64],#[1,2,4,8,16],#[1,2,4],#[1,2,4,8,16],#[1,2,4,8,16],#[1,2,4],#[1,2,4],#[1,2,4,8,16],#[1,2,4],#[2,4,7],#[257,258,260,264,272,288,320,256],#[1,2,4,8,16,32,64],#[1,2112,2118,2058,2050,80,64],#[1,2,4,8,16,32,64],#[1,2,4,8,16],#[17,18,20,16],#[1,2,4,8,16],#[1,2,4,8,16],#[1,2,4,8,16],#[17,18,20,16]] : Array (Array ℕ))[p.val]!)[j]!
def radicalCoefficient (p : Fin 71) (j : Fin (charts (denominatorIndex p)).1)
    (i : Fin (radicalCharts (targetIndex p)).1) : ZMod 2 :=
  if (coefficientMask p j).testBit i.val then 1 else 0
def productCoefficient (p : Fin 71) (j : Fin (charts (denominatorIndex p)).1)
    (i : Fin (charts 14).1) (k : Fin (charts (sourceIndex p)).1) : ZMod 2 :=
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
          ((charts 14).2.inclusion (Pi.single i 1) *
            (charts (sourceIndex p)).2.inclusion (Pi.single k 1)) := by
  decide +kernel

def certificate (p : Fin 71) : BinaryPairLayerDenominatorCertificate rho
    (states (targetIndex p)) (charts 14).2 (charts (sourceIndex p)).2
      (radicalCharts (targetIndex p)).2 (charts (denominatorIndex p)).2 where
  space_le_state := (charts (denominatorIndex p)).2.le_of_basis_mem _ (denominator_basis_mem p)
  radicalCoefficient := radicalCoefficient p
  productCoefficient := productCoefficient p
  basis_eq := denominator_basis_eq p

private theorem scalar_bound : ∀ p : Fin 71,
    headCeiling (sourceIndex p) + (charts (targetIndex p)).1 ≤
      (charts (denominatorIndex p)).1 + 4 := by decide +kernel

theorem finite_pair_bound (p : Fin 71)
    (hproduct : binaryCoordinateProductSpan (charts 14).2.space
      (states (sourceIndex p)).toSubmodule ≤ (states (targetIndex p)).toSubmodule) :
    Module.finrank (ZMod 2) (states (sourceIndex p)).toRepresentation.Coinvariants +
      Module.finrank (ZMod 2) ((states (targetIndex p)).toSubmodule ⧸
        ((binaryCoordinateProductSpan (charts 14).2.space
          (states (sourceIndex p)).toSubmodule).comap (states (targetIndex p)).toSubmodule.subtype ⊔
            Representation.Coinvariants.ker (states (targetIndex p)).toRepresentation)) ≤ 4 := by
  let D := (binaryCoordinateProductSpan (charts 14).2.space
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
    Module.finrank (ZMod 2) ((states (targetIndex p)).toSubmodule ⧸ D) ≤ 4
  omega

def compatible (i j : Fin 15) : Prop := ∀ a : Fin (charts 14).1,
  ∀ b : Fin (charts i).1,
    (charts 14).2.inclusion (Pi.single a 1) * (charts i).2.inclusion (Pi.single b 1) ∈
      (charts j).2.space
theorem covered : ∀ i j : Fin 15, compatible i j →
    ∃ p : Fin 71, sourceIndex p = i ∧ targetIndex p = j := by
  unfold compatible
  intro i
  fin_cases i <;> decide +kernel

theorem wide_indices : ∀ p : Fin 71,
    (charts (denominatorIndex p)).1 + 4 ≤
      headCeiling (sourceIndex p) + (charts (targetIndex p)).1 →
    (sourceIndex p = 14 ∧ targetIndex p = 12) := by decide +kernel

/-- The sparse denominator chart bounds the actual quotient. -/
theorem denominator_dimension_le (p : Fin 71)
    (hproduct : binaryCoordinateProductSpan (charts 14).2.space
      (states (sourceIndex p)).toSubmodule ≤ (states (targetIndex p)).toSubmodule) :
    (charts (denominatorIndex p)).1 +
      Module.finrank (ZMod 2) ((states (targetIndex p)).toSubmodule ⧸
        ((binaryCoordinateProductSpan (charts 14).2.space
          (states (sourceIndex p)).toSubmodule).comap (states (targetIndex p)).toSubmodule.subtype ⊔
            Representation.Coinvariants.ker (states (targetIndex p)).toRepresentation)) ≤
      (charts (targetIndex p)).1 := by
  let D := (binaryCoordinateProductSpan (charts 14).2.space
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

end SymmetricSubgroupAsymptotics.BinaryPairLayerHead8T22Kernel14
