import SymmetricSubgroupAsymptotics.BinaryPairLayerDenominatorCertificate
import SymmetricSubgroupAsymptotics.BinaryRegularEightNaturalRegistryRadicals
import SymmetricSubgroupAsymptotics.BinaryRegularEightNaturalRegistryComplete

set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
noncomputable section
open scoped BigOperators Classical
namespace SymmetricSubgroupAsymptotics.BinaryPairLayerHead8T3Kernel46
open BinaryRegularEightNaturalRegistry

def sourceIndex : Fin 131 → Fin 47 := ![0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,2,3,4,5,6,7,8,9,10,11,12,13,13,13,14,15,16,16,16,17,17,17,18,19,19,19,20,20,20,21,21,21,22,22,22,23,23,23,23,23,23,23,23,23,23,23,23,23,23,23,23,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37,38,38,39,39,40,40,41,41,42,42,43,43,44,44,45,46,46]
def targetIndex : Fin 131 → Fin 47 := ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,1,1,1,1,1,1,1,1,1,1,1,1,1,32,45,1,1,1,28,45,1,26,45,1,1,25,45,1,29,45,1,31,45,1,24,45,1,24,25,26,27,28,29,30,31,32,33,34,35,36,37,45,46,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,45,1,45,1,45,1,45,1,45,1,45,1,45,1,1,45]
def denominatorIndex : Fin 131 → Fin 47 := ![0,45,43,42,40,41,39,38,44,44,41,42,43,23,39,40,23,23,38,23,23,23,23,0,46,46,46,43,46,46,42,46,46,40,41,39,38,44,23,23,23,23,23,23,23,46,23,1,1,1,1,1,1,1,1,1,1,1,1,45,32,32,1,1,45,28,28,45,26,26,1,45,25,25,45,29,29,45,31,31,45,24,24,45,46,46,46,46,46,46,46,46,46,46,46,46,46,46,46,46,1,1,1,1,1,1,1,1,1,1,1,1,1,1,45,45,45,45,45,45,45,45,45,45,45,45,45,45,1,45,45]
def coefficientMask (p : Fin 131) (j : ℕ) : ℕ :=
  ((#[#[],#[1,2,4,8,16,32,64],#[1,2,4],#[1,2,4],#[1,2,4],#[1,2,4],#[1,2,4],#[1,2,4],#[1,2,4],#[1,2,4],#[1,2,4],#[1,2,4],#[1,2,4],#[1],#[1,2,4],#[1,2,4],#[1],#[1],#[1,2,4],#[1],#[1],#[1],#[1],#[],#[1,2,4,8],#[1,2,4,8],#[1,2,4,8],#[1,2,4],#[1,2,4,8],#[1,2,4,8],#[1,2,4],#[1,2,4,8],#[1,2,4,8],#[1,2,4],#[1,2,4],#[1,2,4],#[1,2,4],#[1,2,4],#[1],#[1],#[1],#[1],#[1],#[1],#[1],#[1,2,4,8],#[1],#[128,131,133,137,145,161,193,129],#[32801,32802,32804,32808,32816,32768,32864,32800],#[2113,2114,2116,2120,2128,2144,2048,2112],#[2049,2050,2052,2056,2064,2080,2112,2048],#[128,131,133,137,145,161,193,129],#[128,131,133,137,145,161,193,129],#[128,131,133,137,145,161,193,129],#[224,227,229,233,241,193,161,225],#[128,131,133,137,145,161,193,129],#[224,227,229,233,241,193,161,225],#[4179,4176,4182,4186,4162,4210,4114,4178],#[131125,131126,131120,131132,131108,131092,131188,131124],#[1,2,4,8,16,32,64],#[16,64,87,91,66,17],#[16,64,87,91,66,17],#[160,163,165,169,177,129,225,161],#[4115,4112,4118,4122,4098,4146,4178,4114],#[1,2,4,8,16,32,64],#[16,64,87,91,66,17],#[16,64,87,91,66,17],#[1,2,4,8,16,32,64],#[16,275,260,281,256,17],#[16,275,260,281,256,17],#[192,195,197,201,209,225,129,193],#[1,2,4,8,16,32,64],#[16,279,256,285,260,17],#[16,279,256,285,260,17],#[1,2,4,8,16,32,64],#[16,66,85,89,64,17],#[16,66,85,89,64,17],#[1,2,4,8,16,32,64],#[16,66,85,89,64,17],#[16,66,85,89,64,17],#[1,2,4,8,16,32,64],#[321,66,260,328,256,64],#[321,66,260,328,256,64],#[1,2,4,8,16,32,64],#[1,2,4,8],#[1,2,4,8],#[1,2,4,8],#[1,2,32,36],#[1,2,4,8],#[1,2,4,8],#[1,16,4,18],#[1,2,4,8],#[1,2,4,8],#[1,16,18,4],#[8,2,4,9],#[8,2,9,4],#[8,9,2,4],#[8,11,13,9],#[1,2,4,8],#[2,4,8,15],#[8193,8194,8196,8200,8208,8224,8256,8192],#[257,258,260,264,272,288,320,256],#[289,290,292,296,304,256,352,288],#[131105,131106,131108,131112,131120,131072,131168,131104],#[321,322,324,328,336,352,256,320],#[257,258,260,264,272,288,320,256],#[4161,4162,4164,4168,4176,4192,4096,4160],#[321,322,324,328,336,352,256,320],#[257,258,260,264,272,288,320,256],#[4097,4098,4100,4104,4112,4128,4160,4096],#[321,322,324,328,336,352,256,320],#[257,258,260,264,272,288,320,256],#[353,354,356,360,368,320,288,352],#[289,290,292,296,304,256,352,288],#[1,2,4,8,16,32,64],#[48,275,292,313,256,32,17],#[1,2,4,8,16,32,64],#[48,130,181,153,160,17,32],#[1,2,4,8,16,32,64],#[33,384,422,298,258,160,128],#[1,2,4,8,16,32,64],#[16,162,181,153,128,49,32],#[1,2,4,8,16,32,64],#[161,256,422,298,386,32,128],#[1,2,4,8,16,32,64],#[1057,2082,3076,3112,2048,1024,32],#[1,2,4,8,16,32,64],#[16,179,164,153,128,32,49],#[257,258,260,264,272,288,320,256],#[1,2,4,8,16,32,64],#[97,1058,1092,1128,1024,64,32]] : Array (Array ℕ))[p.val]!)[j]!
def radicalCoefficient (p : Fin 131) (j : Fin (charts (denominatorIndex p)).1)
    (i : Fin (radicalCharts (targetIndex p)).1) : ZMod 2 :=
  if (coefficientMask p j).testBit i.val then 1 else 0
def productCoefficient (p : Fin 131) (j : Fin (charts (denominatorIndex p)).1)
    (i : Fin (charts 46).1) (k : Fin (charts (sourceIndex p)).1) : ZMod 2 :=
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
          ((charts 46).2.inclusion (Pi.single i 1) *
            (charts (sourceIndex p)).2.inclusion (Pi.single k 1)) := by
  decide +kernel

def certificate (p : Fin 131) : BinaryPairLayerDenominatorCertificate rho
    (states (targetIndex p)) (charts 46).2 (charts (sourceIndex p)).2
      (radicalCharts (targetIndex p)).2 (charts (denominatorIndex p)).2 where
  space_le_state := (charts (denominatorIndex p)).2.le_of_basis_mem _ (denominator_basis_mem p)
  radicalCoefficient := radicalCoefficient p
  productCoefficient := productCoefficient p
  basis_eq := denominator_basis_eq p

private theorem scalar_bound : ∀ p : Fin 131,
    headCeiling (sourceIndex p) + (charts (targetIndex p)).1 ≤
      (charts (denominatorIndex p)).1 + 4 := by decide +kernel

theorem finite_pair_bound (p : Fin 131)
    (hproduct : binaryCoordinateProductSpan (charts 46).2.space
      (states (sourceIndex p)).toSubmodule ≤ (states (targetIndex p)).toSubmodule) :
    Module.finrank (ZMod 2) (states (sourceIndex p)).toRepresentation.Coinvariants +
      Module.finrank (ZMod 2) ((states (targetIndex p)).toSubmodule ⧸
        ((binaryCoordinateProductSpan (charts 46).2.space
          (states (sourceIndex p)).toSubmodule).comap (states (targetIndex p)).toSubmodule.subtype ⊔
            Representation.Coinvariants.ker (states (targetIndex p)).toRepresentation)) ≤ 4 := by
  let D := (binaryCoordinateProductSpan (charts 46).2.space
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

def compatible (i j : Fin 47) : Prop := ∀ a : Fin (charts 46).1,
  ∀ b : Fin (charts i).1,
    (charts 46).2.inclusion (Pi.single a 1) * (charts i).2.inclusion (Pi.single b 1) ∈
      (charts j).2.space
theorem covered : ∀ i j : Fin 47, compatible i j →
    ∃ p : Fin 131, sourceIndex p = i ∧ targetIndex p = j := by
  unfold compatible
  intro i
  fin_cases i <;> decide +kernel

theorem wide_indices : ∀ p : Fin 131,
    (charts (denominatorIndex p)).1 + 4 ≤
      headCeiling (sourceIndex p) + (charts (targetIndex p)).1 →
    (sourceIndex p = 23 ∧ targetIndex p = 45) ∨ (sourceIndex p = 46 ∧ targetIndex p = 1) := by decide +kernel

/-- The sparse denominator chart bounds the actual quotient. -/
theorem denominator_dimension_le (p : Fin 131)
    (hproduct : binaryCoordinateProductSpan (charts 46).2.space
      (states (sourceIndex p)).toSubmodule ≤ (states (targetIndex p)).toSubmodule) :
    (charts (denominatorIndex p)).1 +
      Module.finrank (ZMod 2) ((states (targetIndex p)).toSubmodule ⧸
        ((binaryCoordinateProductSpan (charts 46).2.space
          (states (sourceIndex p)).toSubmodule).comap (states (targetIndex p)).toSubmodule.subtype ⊔
            Representation.Coinvariants.ker (states (targetIndex p)).toRepresentation)) ≤
      (charts (targetIndex p)).1 := by
  let D := (binaryCoordinateProductSpan (charts 46).2.space
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

end SymmetricSubgroupAsymptotics.BinaryPairLayerHead8T3Kernel46
