import SymmetricSubgroupAsymptotics.BinaryCoordinateFixedDisplacementCard
import SymmetricSubgroupAsymptotics.BinaryRegular46FullConstantOuterCarriesData
import SymmetricSubgroupAsymptotics.BinarySplitRegular46FullConstantStabilizerData
import Mathlib.Data.Fintype.Pi
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
noncomputable section
open scoped BigOperators Classical
namespace SymmetricSubgroupAsymptotics.BinaryRegularFullConstantPlaneOne
local instance planeOneFactPrimeTwo : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
abbrev V := Fin 16 → ZMod 2
abbrev K := BinarySplitRegular46FullConstantStabilizer.state
private def planeInclusion := (binaryRectangularMatrixOfColumnMasks 16 2 (![255,135] : Fin 2 → ℕ)).mulVecLin
private def planeCoordinates := (binaryRectangularMatrixOfColumnMasks 2 16
  (fun i => binaryVectorMask (fun j => binaryVectorOfMask 16 ((![8,9] : Fin 2 → ℕ) j) i))).mulVecLin
private theorem plane_basis : ∀ j : Fin 2,planeCoordinates (planeInclusion (Pi.single j 1))=Pi.single j 1 := by decide +kernel
private theorem plane_left (v : Fin 2 → ZMod 2) : planeCoordinates (planeInclusion v)=v := by
  have he : planeCoordinates.comp planeInclusion=LinearMap.id := by
    apply LinearMap.pi_ext
    intro i c
    have hs : Pi.single i c=c • Pi.single i (1 : ZMod 2) := by ext j;simp [Pi.single_apply,mul_ite]
    simp only [LinearMap.comp_apply,hs,map_smul,plane_basis,LinearMap.id_apply]
  exact DFunLike.congr_fun he v
def plane : BinaryCoordinateSpace 16 2 := ⟨planeInclusion,planeCoordinates,plane_left⟩
def action (i : Fin 6) : V →ₗ[ZMod 2] V :=
  BinaryRegular46FullConstantOuterCarries.layerChange.comp
    (((binaryPermutationRepresentation 16) (BinaryRegular46FullConstantOuterCarries.generators i)).comp
      BinaryRegular46FullConstantOuterCarries.layerChange)
private def annMasks : Fin 14 → ℕ := ![129,130,132,72,80,96,256,512,1024,2048,4096,8192,16384,32768]
private def genIndex : Fin 8 → Fin 6 := ![0,0,1,1,3,3,5,5]
private def annIndex : Fin 8 → Fin 14 := ![0,1,0,4,1,3,0,1]
private def inputMasks : Fin 8 → ℕ := ![6,10,7,2,3600,480,2448,1360]
private def basisMasks : Fin 4 → ℕ := ![3600,3360,2880,1920]
private def coordinateMasks : Fin 12 → ℕ := ![0,0,0,0,1,2,4,8,0,0,0,0]
private def combinations : Fin 12 → ℕ := ![5,8,9,10,0,0,0,0,32,208,160,96]
private def inclusion := (binaryRectangularMatrixOfColumnMasks 12 4 basisMasks).mulVecLin
private def coordinates := (binaryRectangularMatrixOfColumnMasks 4 12 coordinateMasks).mulVecLin
private theorem chart_basis : ∀ j : Fin 4,coordinates (inclusion (Pi.single j 1))=Pi.single j 1 := by decide +kernel
private theorem chart_left (v : Fin 4 → ZMod 2) : coordinates (inclusion v)=v := by
  have he : coordinates.comp inclusion=LinearMap.id := by
    apply LinearMap.pi_ext
    intro i c
    have hs : Pi.single i c=c • Pi.single i (1 : ZMod 2) := by ext j;simp [Pi.single_apply,mul_ite]
    simp only [LinearMap.comp_apply,hs,map_smul,chart_basis,LinearMap.id_apply]
  exact DFunLike.congr_fun he v
private def chart : BinaryCoordinateSpace 12 4 := ⟨inclusion,coordinates,chart_left⟩
private def input (i : Fin 8) := binaryVectorOfMask 12 (inputMasks i)
private def ann (i : Fin 8) := binaryRowFunctional (binaryVectorOfMask 16 (annMasks (annIndex i)))
private def rowCertificate : BinaryLinearConstraintCertificate input (binaryCoordinateDefectRows chart) where
  support j := Finset.univ.filter fun i => (combinations j).testBit i.val
  target_eq := by decide +kernel
private theorem input_basis : ∀ i : Fin 8,∀ j : Fin 12,
  binaryRowFunctional (input i) (Pi.single j 1)=
    ((ann i).comp ((action (genIndex i)-LinearMap.id).comp K.inclusion)) (Pi.single j 1) := by decide +kernel
private theorem ann_kill_basis : ∀ i : Fin 8,∀ j : Fin 2,
  ann i (plane.inclusion (Pi.single j 1))=0 := by decide +kernel
theorem fixed_card_le : Nat.card (binaryCoordinateFixedDisplacements K action plane.space)≤16 := by
  apply binaryCoordinateFixedDisplacements_card_le_of_certificate K action plane.space ann genIndex chart input rowCertificate
    (fun i => binaryLinearFunctional_ext_basis (input_basis i))
  intro i v hv
  have hle : plane.space≤(ann i).ker := plane.le_of_basis_mem (ann i).ker (fun j => ann_kill_basis i j)
  exact hle hv
private def candidateImages : Fin 2 → Fin 16 → Fin 16 := ![![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15],![8,9,10,11,12,13,14,15,0,1,2,3,4,5,6,7]]
private theorem candidate_inv : ∀ i j,candidateImages i (candidateImages i j)=j := by decide +kernel
def candidate (i : Fin 2) : Equiv.Perm (Fin 16) := {toFun:=candidateImages i,invFun:=candidateImages i,left_inv:=candidate_inv i,right_inv:=candidate_inv i}
def candidateAction (i : Fin 2) : V →ₗ[ZMod 2] V :=
  BinaryRegular46FullConstantOuterCarries.layerChange.comp
    (((binaryPermutationRepresentation 16) (candidate i)).comp BinaryRegular46FullConstantOuterCarries.layerChange)
private theorem allowed_test : ∀ i : Fin 2,
    (∀ j : Fin 12,candidateAction i (K.inclusion (Pi.single j 1))-K.inclusion (Pi.single j 1)∈plane.space) → i=0 := by
  simp only [BinaryCoordinateSpace.mem_iff]
  decide +kernel
theorem allowed_card_le : Nat.card {i : Fin 2 // ∀ j : Fin 12,
    candidateAction i (K.inclusion (Pi.single j 1))-K.inclusion (Pi.single j 1)∈plane.space}≤1 := by
  have hs : Subsingleton {i : Fin 2 // ∀ j : Fin 12,
    candidateAction i (K.inclusion (Pi.single j 1))-K.inclusion (Pi.single j 1)∈plane.space} := ⟨fun a b => Subtype.ext ((allowed_test a.val a.property).trans (allowed_test b.val b.property).symm)⟩
  letI := hs
  have hc := Nat.card_le_card_of_injective
    (fun _ : {i : Fin 2 // ∀ j : Fin 12,
      candidateAction i (K.inclusion (Pi.single j 1))-K.inclusion (Pi.single j 1)∈plane.space} => (() : Unit))
    (fun a b _ => Subsingleton.elim a b)
  simpa only [Nat.card_unique] using hc
end SymmetricSubgroupAsymptotics.BinaryRegularFullConstantPlaneOne
