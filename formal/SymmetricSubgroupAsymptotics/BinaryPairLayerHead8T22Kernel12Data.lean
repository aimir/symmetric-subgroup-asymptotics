import SymmetricSubgroupAsymptotics.BinaryPairLayerDenominatorCertificate
import SymmetricSubgroupAsymptotics.BinaryHeisenbergEightNaturalHeads
import SymmetricSubgroupAsymptotics.BinaryHeisenbergEightNaturalCarrySpaces

set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
noncomputable section
open scoped BigOperators Classical
namespace SymmetricSubgroupAsymptotics.BinaryPairLayerHead8T22Kernel12
open BinaryHeisenbergEightNaturalHeads

def sourceIndex : Fin 30 → Fin 15 := ![0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,2,3,4,5,6,7,8,9,10,11,11,12,13,14]
def targetIndex : Fin 30 → Fin 15 := ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,1,1,1,1,1,1,1,1,1,1,1,12,1,1,1]
def denominatorIndex : Fin 30 → Fin 15 := ![0,12,13,14,13,13,11,14,14,11,11,0,13,14,11,1,1,1,1,1,1,1,1,1,1,12,12,1,1,1]
def coefficientMask (p : Fin 30) (j : ℕ) : ℕ :=
  ((#[#[],#[1,2,4,8,16,32,64],#[1,2,4,8,16],#[1,2,4],#[1,2,4,8,16],#[1,2,4,8,16],#[1],#[1,2,4],#[1,2,4],#[1],#[1],#[],#[1,2,4,8,16],#[1,2,4],#[1],#[128,131,133,137,145,161,193,129],#[2049,2050,2052,2056,2064,2080,2112,2048],#[2049,2050,2052,2056,2064,2080,2112,2048],#[1025,1026,1028,1032,1040,1056,1088,1024],#[257,258,260,264,272,288,320,256],#[8193,8194,8196,8200,8208,8224,8256,8192],#[257,258,260,264,272,288,320,256],#[257,258,260,264,272,288,320,256],#[513,514,516,520,528,544,576,512],#[513,514,516,520,528,544,576,512],#[1,2,4,8,16,32,64],#[1,64,70,256,264,346,330],#[257,258,260,264,272,288,320,256],#[257,258,260,264,272,288,320,256],#[1025,1026,1028,1032,1040,1056,1088,1024]] : Array (Array ℕ))[p.val]!)[j]!
def radicalCoefficient (p : Fin 30) (j : Fin (charts (denominatorIndex p)).1)
    (i : Fin (radicalCharts (targetIndex p)).1) : ZMod 2 :=
  if (coefficientMask p j).testBit i.val then 1 else 0
def productCoefficient (p : Fin 30) (j : Fin (charts (denominatorIndex p)).1)
    (i : Fin (charts 12).1) (k : Fin (charts (sourceIndex p)).1) : ZMod 2 :=
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
          ((charts 12).2.inclusion (Pi.single i 1) *
            (charts (sourceIndex p)).2.inclusion (Pi.single k 1)) := by
  decide +kernel

def certificate (p : Fin 30) : BinaryPairLayerDenominatorCertificate rho
    (states (targetIndex p)) (charts 12).2 (charts (sourceIndex p)).2
      (radicalCharts (targetIndex p)).2 (charts (denominatorIndex p)).2 where
  space_le_state := (charts (denominatorIndex p)).2.le_of_basis_mem _ (denominator_basis_mem p)
  radicalCoefficient := radicalCoefficient p
  productCoefficient := productCoefficient p
  basis_eq := denominator_basis_eq p

private theorem scalar_bound : ∀ p : Fin 30,
    headCeiling (sourceIndex p) + (charts (targetIndex p)).1 ≤
      (charts (denominatorIndex p)).1 + 2 := by decide +kernel

theorem finite_pair_bound (p : Fin 30)
    (hproduct : binaryCoordinateProductSpan (charts 12).2.space
      (states (sourceIndex p)).toSubmodule ≤ (states (targetIndex p)).toSubmodule) :
    Module.finrank (ZMod 2) (states (sourceIndex p)).toRepresentation.Coinvariants +
      Module.finrank (ZMod 2) ((states (targetIndex p)).toSubmodule ⧸
        ((binaryCoordinateProductSpan (charts 12).2.space
          (states (sourceIndex p)).toSubmodule).comap (states (targetIndex p)).toSubmodule.subtype ⊔
            Representation.Coinvariants.ker (states (targetIndex p)).toRepresentation)) ≤ 2 := by
  let D := (binaryCoordinateProductSpan (charts 12).2.space
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
    Module.finrank (ZMod 2) ((states (targetIndex p)).toSubmodule ⧸ D) ≤ 2
  omega

def compatible (i j : Fin 15) : Prop := ∀ a : Fin (charts 12).1,
  ∀ b : Fin (charts i).1,
    (charts 12).2.inclusion (Pi.single a 1) * (charts i).2.inclusion (Pi.single b 1) ∈
      (charts j).2.space
theorem covered : ∀ i j : Fin 15, compatible i j →
    ∃ p : Fin 30, sourceIndex p = i ∧ targetIndex p = j := by
  unfold compatible
  intro i
  fin_cases i <;> decide +kernel

end SymmetricSubgroupAsymptotics.BinaryPairLayerHead8T22Kernel12
