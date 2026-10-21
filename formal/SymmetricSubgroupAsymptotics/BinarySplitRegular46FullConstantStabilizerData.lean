import SymmetricSubgroupAsymptotics.BinarySplitAffineFunctionCoordinates
import SymmetricSubgroupAsymptotics.FiniteEightRowSlices
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.FinCases
import SymmetricSubgroupAsymptotics.LinearStabilizerQuotientRepresentatives
import SymmetricSubgroupAsymptotics.BinaryBitmaskCoordinates
import Mathlib.Algebra.Field.ZMod

/-! A selected original split-layer point-stabilizer certificate. All
row actions are literal affine formulas; completeness is a separate
bijective original-row hypothesis supplied by the full-model bridge. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.BinarySplitRegular46FullConstantStabilizer
local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
abbrev V := Fin 16 → ZMod 2
private def wBasis : Fin 12 → ℕ := ![34560,19200,11520,7680,128,64,32,16,8,4,2,1]
private def wDual : Fin 12 → ℕ := ![32768,16384,8192,4096,128,64,32,16,8,4,2,1]
private def rBasis : Fin 8 → ℕ := ![65280,129,65,33,17,9,5,3]
private def rDual : Fin 8 → ℕ := ![32768,128,64,32,16,8,4,2]
private def wInclusion := (binaryRectangularMatrixOfColumnMasks 16 12 wBasis).mulVecLin
private def wCoordinates := (binaryRectangularMatrixOfColumnMasks 12 16
  (fun i => binaryVectorMask (fun j => (binaryVectorOfMask 16 (wDual j)) i)) ).mulVecLin
private def rInclusion := (binaryRectangularMatrixOfColumnMasks 16 8 rBasis).mulVecLin
private def rCoordinates := (binaryRectangularMatrixOfColumnMasks 8 16
  (fun i => binaryVectorMask (fun j => (binaryVectorOfMask 16 (rDual j)) i)) ).mulVecLin
private theorem w_basis : ∀ i : Fin 12,
    wCoordinates (wInclusion (Pi.single i 1)) = Pi.single i 1 := by decide +kernel
private theorem r_basis : ∀ i : Fin 8,
    rCoordinates (rInclusion (Pi.single i 1)) = Pi.single i 1 := by decide +kernel
private theorem w_left_inverse (v : Fin 12 → ZMod 2) : wCoordinates (wInclusion v) = v := by
  have he : wCoordinates.comp wInclusion = LinearMap.id := by
    apply LinearMap.pi_ext
    intro i c
    have hs : Pi.single i c = c • Pi.single i (1 : ZMod 2) := by
      ext j
      simp [Pi.single_apply, mul_ite]
    simp only [LinearMap.comp_apply, hs, map_smul, w_basis, LinearMap.id_apply]
  exact DFunLike.congr_fun he v
private theorem r_left_inverse (v : Fin 8 → ZMod 2) : rCoordinates (rInclusion v) = v := by
  have he : rCoordinates.comp rInclusion = LinearMap.id := by
    apply LinearMap.pi_ext
    intro i c
    have hs : Pi.single i c = c • Pi.single i (1 : ZMod 2) := by
      ext j
      simp [Pi.single_apply, mul_ite]
    simp only [LinearMap.comp_apply, hs, map_smul, r_basis, LinearMap.id_apply]
  exact DFunLike.congr_fun he v

def state : BinaryCoordinateSpace 16 12 := ⟨wInclusion, wCoordinates, w_left_inverse⟩
def radical : BinaryCoordinateSpace 16 8 := ⟨rInclusion, rCoordinates, r_left_inverse⟩
def projection := (binaryRectangularMatrixOfColumnMasks 4 16
  (![0,0,0,0,0,0,0,0,1,2,4,8,14,13,11,7] : Fin 16 → ℕ)).mulVecLin
def sectionMap := (binaryRectangularMatrixOfColumnMasks 16 4
  (![256,512,1024,2048] : Fin 4 → ℕ)).mulVecLin
private def inverseImages : Fin 128 → Fin 8 → Fin 8 := ![![0,1,2,3,4,5,6,7],![0,1,2,3,4,5,6,7],![0,1,2,3,4,5,6,7],![0,1,2,3,4,5,6,7],![0,1,2,3,4,5,6,7],![0,1,2,3,4,5,6,7],![0,1,2,3,4,5,6,7],![0,1,2,3,4,5,6,7],![0,1,2,3,4,5,6,7],![0,1,2,3,4,5,6,7],![0,1,2,3,4,5,6,7],![0,1,2,3,4,5,6,7],![0,1,2,3,4,5,6,7],![0,1,2,3,4,5,6,7],![0,1,2,3,4,5,6,7],![0,1,2,3,4,5,6,7],![1,0,7,6,5,4,3,2],![1,0,7,6,5,4,3,2],![1,0,7,6,5,4,3,2],![1,0,7,6,5,4,3,2],![1,0,7,6,5,4,3,2],![1,0,7,6,5,4,3,2],![1,0,7,6,5,4,3,2],![1,0,7,6,5,4,3,2],![1,0,7,6,5,4,3,2],![1,0,7,6,5,4,3,2],![1,0,7,6,5,4,3,2],![1,0,7,6,5,4,3,2],![1,0,7,6,5,4,3,2],![1,0,7,6,5,4,3,2],![1,0,7,6,5,4,3,2],![1,0,7,6,5,4,3,2],![2,7,0,5,6,3,4,1],![2,7,0,5,6,3,4,1],![2,7,0,5,6,3,4,1],![2,7,0,5,6,3,4,1],![2,7,0,5,6,3,4,1],![2,7,0,5,6,3,4,1],![2,7,0,5,6,3,4,1],![2,7,0,5,6,3,4,1],![2,7,0,5,6,3,4,1],![2,7,0,5,6,3,4,1],![2,7,0,5,6,3,4,1],![2,7,0,5,6,3,4,1],![2,7,0,5,6,3,4,1],![2,7,0,5,6,3,4,1],![2,7,0,5,6,3,4,1],![2,7,0,5,6,3,4,1],![3,6,5,0,7,2,1,4],![3,6,5,0,7,2,1,4],![3,6,5,0,7,2,1,4],![3,6,5,0,7,2,1,4],![3,6,5,0,7,2,1,4],![3,6,5,0,7,2,1,4],![3,6,5,0,7,2,1,4],![3,6,5,0,7,2,1,4],![3,6,5,0,7,2,1,4],![3,6,5,0,7,2,1,4],![3,6,5,0,7,2,1,4],![3,6,5,0,7,2,1,4],![3,6,5,0,7,2,1,4],![3,6,5,0,7,2,1,4],![3,6,5,0,7,2,1,4],![3,6,5,0,7,2,1,4],![4,5,6,7,0,1,2,3],![4,5,6,7,0,1,2,3],![4,5,6,7,0,1,2,3],![4,5,6,7,0,1,2,3],![4,5,6,7,0,1,2,3],![4,5,6,7,0,1,2,3],![4,5,6,7,0,1,2,3],![4,5,6,7,0,1,2,3],![4,5,6,7,0,1,2,3],![4,5,6,7,0,1,2,3],![4,5,6,7,0,1,2,3],![4,5,6,7,0,1,2,3],![4,5,6,7,0,1,2,3],![4,5,6,7,0,1,2,3],![4,5,6,7,0,1,2,3],![4,5,6,7,0,1,2,3],![5,4,3,2,1,0,7,6],![5,4,3,2,1,0,7,6],![5,4,3,2,1,0,7,6],![5,4,3,2,1,0,7,6],![5,4,3,2,1,0,7,6],![5,4,3,2,1,0,7,6],![5,4,3,2,1,0,7,6],![5,4,3,2,1,0,7,6],![5,4,3,2,1,0,7,6],![5,4,3,2,1,0,7,6],![5,4,3,2,1,0,7,6],![5,4,3,2,1,0,7,6],![5,4,3,2,1,0,7,6],![5,4,3,2,1,0,7,6],![5,4,3,2,1,0,7,6],![5,4,3,2,1,0,7,6],![6,3,4,1,2,7,0,5],![6,3,4,1,2,7,0,5],![6,3,4,1,2,7,0,5],![6,3,4,1,2,7,0,5],![6,3,4,1,2,7,0,5],![6,3,4,1,2,7,0,5],![6,3,4,1,2,7,0,5],![6,3,4,1,2,7,0,5],![6,3,4,1,2,7,0,5],![6,3,4,1,2,7,0,5],![6,3,4,1,2,7,0,5],![6,3,4,1,2,7,0,5],![6,3,4,1,2,7,0,5],![6,3,4,1,2,7,0,5],![6,3,4,1,2,7,0,5],![6,3,4,1,2,7,0,5],![7,2,1,4,3,6,5,0],![7,2,1,4,3,6,5,0],![7,2,1,4,3,6,5,0],![7,2,1,4,3,6,5,0],![7,2,1,4,3,6,5,0],![7,2,1,4,3,6,5,0],![7,2,1,4,3,6,5,0],![7,2,1,4,3,6,5,0],![7,2,1,4,3,6,5,0],![7,2,1,4,3,6,5,0],![7,2,1,4,3,6,5,0],![7,2,1,4,3,6,5,0],![7,2,1,4,3,6,5,0],![7,2,1,4,3,6,5,0],![7,2,1,4,3,6,5,0],![7,2,1,4,3,6,5,0]]
private def forwardImages : Fin 128 → Fin 8 → Fin 8 := ![![0,1,2,3,4,5,6,7],![0,1,2,3,4,5,6,7],![0,1,2,3,4,5,6,7],![0,1,2,3,4,5,6,7],![0,1,2,3,4,5,6,7],![0,1,2,3,4,5,6,7],![0,1,2,3,4,5,6,7],![0,1,2,3,4,5,6,7],![0,1,2,3,4,5,6,7],![0,1,2,3,4,5,6,7],![0,1,2,3,4,5,6,7],![0,1,2,3,4,5,6,7],![0,1,2,3,4,5,6,7],![0,1,2,3,4,5,6,7],![0,1,2,3,4,5,6,7],![0,1,2,3,4,5,6,7],![1,0,7,6,5,4,3,2],![1,0,7,6,5,4,3,2],![1,0,7,6,5,4,3,2],![1,0,7,6,5,4,3,2],![1,0,7,6,5,4,3,2],![1,0,7,6,5,4,3,2],![1,0,7,6,5,4,3,2],![1,0,7,6,5,4,3,2],![1,0,7,6,5,4,3,2],![1,0,7,6,5,4,3,2],![1,0,7,6,5,4,3,2],![1,0,7,6,5,4,3,2],![1,0,7,6,5,4,3,2],![1,0,7,6,5,4,3,2],![1,0,7,6,5,4,3,2],![1,0,7,6,5,4,3,2],![2,7,0,5,6,3,4,1],![2,7,0,5,6,3,4,1],![2,7,0,5,6,3,4,1],![2,7,0,5,6,3,4,1],![2,7,0,5,6,3,4,1],![2,7,0,5,6,3,4,1],![2,7,0,5,6,3,4,1],![2,7,0,5,6,3,4,1],![2,7,0,5,6,3,4,1],![2,7,0,5,6,3,4,1],![2,7,0,5,6,3,4,1],![2,7,0,5,6,3,4,1],![2,7,0,5,6,3,4,1],![2,7,0,5,6,3,4,1],![2,7,0,5,6,3,4,1],![2,7,0,5,6,3,4,1],![3,6,5,0,7,2,1,4],![3,6,5,0,7,2,1,4],![3,6,5,0,7,2,1,4],![3,6,5,0,7,2,1,4],![3,6,5,0,7,2,1,4],![3,6,5,0,7,2,1,4],![3,6,5,0,7,2,1,4],![3,6,5,0,7,2,1,4],![3,6,5,0,7,2,1,4],![3,6,5,0,7,2,1,4],![3,6,5,0,7,2,1,4],![3,6,5,0,7,2,1,4],![3,6,5,0,7,2,1,4],![3,6,5,0,7,2,1,4],![3,6,5,0,7,2,1,4],![3,6,5,0,7,2,1,4],![4,5,6,7,0,1,2,3],![4,5,6,7,0,1,2,3],![4,5,6,7,0,1,2,3],![4,5,6,7,0,1,2,3],![4,5,6,7,0,1,2,3],![4,5,6,7,0,1,2,3],![4,5,6,7,0,1,2,3],![4,5,6,7,0,1,2,3],![4,5,6,7,0,1,2,3],![4,5,6,7,0,1,2,3],![4,5,6,7,0,1,2,3],![4,5,6,7,0,1,2,3],![4,5,6,7,0,1,2,3],![4,5,6,7,0,1,2,3],![4,5,6,7,0,1,2,3],![4,5,6,7,0,1,2,3],![5,4,3,2,1,0,7,6],![5,4,3,2,1,0,7,6],![5,4,3,2,1,0,7,6],![5,4,3,2,1,0,7,6],![5,4,3,2,1,0,7,6],![5,4,3,2,1,0,7,6],![5,4,3,2,1,0,7,6],![5,4,3,2,1,0,7,6],![5,4,3,2,1,0,7,6],![5,4,3,2,1,0,7,6],![5,4,3,2,1,0,7,6],![5,4,3,2,1,0,7,6],![5,4,3,2,1,0,7,6],![5,4,3,2,1,0,7,6],![5,4,3,2,1,0,7,6],![5,4,3,2,1,0,7,6],![6,3,4,1,2,7,0,5],![6,3,4,1,2,7,0,5],![6,3,4,1,2,7,0,5],![6,3,4,1,2,7,0,5],![6,3,4,1,2,7,0,5],![6,3,4,1,2,7,0,5],![6,3,4,1,2,7,0,5],![6,3,4,1,2,7,0,5],![6,3,4,1,2,7,0,5],![6,3,4,1,2,7,0,5],![6,3,4,1,2,7,0,5],![6,3,4,1,2,7,0,5],![6,3,4,1,2,7,0,5],![6,3,4,1,2,7,0,5],![6,3,4,1,2,7,0,5],![6,3,4,1,2,7,0,5],![7,2,1,4,3,6,5,0],![7,2,1,4,3,6,5,0],![7,2,1,4,3,6,5,0],![7,2,1,4,3,6,5,0],![7,2,1,4,3,6,5,0],![7,2,1,4,3,6,5,0],![7,2,1,4,3,6,5,0],![7,2,1,4,3,6,5,0],![7,2,1,4,3,6,5,0],![7,2,1,4,3,6,5,0],![7,2,1,4,3,6,5,0],![7,2,1,4,3,6,5,0],![7,2,1,4,3,6,5,0],![7,2,1,4,3,6,5,0],![7,2,1,4,3,6,5,0],![7,2,1,4,3,6,5,0]]
private def offsetMasks : Fin 128 → ℕ := ![0,135,75,204,45,170,102,225,30,153,85,210,51,180,120,255,0,135,75,204,45,170,102,225,30,153,85,210,51,180,120,255,0,135,75,204,45,170,102,225,30,153,85,210,51,180,120,255,0,135,75,204,45,170,102,225,30,153,85,210,51,180,120,255,0,135,75,204,45,170,102,225,30,153,85,210,51,180,120,255,0,135,75,204,45,170,102,225,30,153,85,210,51,180,120,255,0,135,75,204,45,170,102,225,30,153,85,210,51,180,120,255,0,135,75,204,45,170,102,225,30,153,85,210,51,180,120,255]
private theorem images_inverse : ∀ i j, inverseImages i (forwardImages i j) = j := by decide +kernel
private theorem images_forward : ∀ i j, forwardImages i (inverseImages i j) = j := by decide +kernel

def topPermutation (i : Fin 128) : Equiv.Perm (Fin 8) := {
  toFun := forwardImages i
  invFun := inverseImages i
  left_inv := images_inverse i
  right_inv := images_forward i }
def destinationOffset (i : Fin 128) : Fin 8 → ZMod 2 := binaryVectorOfMask 8 (offsetMasks i)
def rowAction (i : Fin 128) : V →ₗ[ZMod 2] V :=
  (BinaryPairFrame.pairLayerFlatten (w := 8)).toLinearMap.comp
    ((BinaryPairFrame.affinePairLayerMap (topPermutation i) (destinationOffset i)).comp
      (BinaryPairFrame.pairLayerFlatten (w := 8)).symm.toLinearMap)
theorem quotient_basis : ∀ j : Fin 16,
    Pi.single j 1 - sectionMap (projection (Pi.single j 1)) ∈ state.space := by
  simp only [BinaryCoordinateSpace.mem_iff]
  decide +kernel
private def killBasisRow (n : Fin 1536) : Prop :=
  rowAction (finProdFinEquiv.symm n : Fin 128 × Fin 12).1
    (state.inclusion (Pi.single (finProdFinEquiv.symm n : Fin 128 × Fin 12).2 1)) -
    state.inclusion (Pi.single (finProdFinEquiv.symm n : Fin 128 × Fin 12).2 1) ∈ radical.space

private theorem kill_basis_block_0 : ∀ s : Fin 8,
    ∀ hs : 8 * 0 + s.val < 1536, killBasisRow ⟨8 * 0 + s.val, hs⟩ := by
  simp only [killBasisRow, BinaryCoordinateSpace.mem_iff]
  decide +kernel

private theorem kill_basis_block_1 : ∀ s : Fin 8,
    ∀ hs : 8 * 1 + s.val < 1536, killBasisRow ⟨8 * 1 + s.val, hs⟩ := by
  simp only [killBasisRow, BinaryCoordinateSpace.mem_iff]
  decide +kernel

private theorem kill_basis_block_2 : ∀ s : Fin 8,
    ∀ hs : 8 * 2 + s.val < 1536, killBasisRow ⟨8 * 2 + s.val, hs⟩ := by
  simp only [killBasisRow, BinaryCoordinateSpace.mem_iff]
  decide +kernel

private theorem kill_basis_block_3 : ∀ s : Fin 8,
    ∀ hs : 8 * 3 + s.val < 1536, killBasisRow ⟨8 * 3 + s.val, hs⟩ := by
  simp only [killBasisRow, BinaryCoordinateSpace.mem_iff]
  decide +kernel

private theorem kill_basis_block_4 : ∀ s : Fin 8,
    ∀ hs : 8 * 4 + s.val < 1536, killBasisRow ⟨8 * 4 + s.val, hs⟩ := by
  simp only [killBasisRow, BinaryCoordinateSpace.mem_iff]
  decide +kernel

private theorem kill_basis_block_5 : ∀ s : Fin 8,
    ∀ hs : 8 * 5 + s.val < 1536, killBasisRow ⟨8 * 5 + s.val, hs⟩ := by
  simp only [killBasisRow, BinaryCoordinateSpace.mem_iff]
  decide +kernel

private theorem kill_basis_block_6 : ∀ s : Fin 8,
    ∀ hs : 8 * 6 + s.val < 1536, killBasisRow ⟨8 * 6 + s.val, hs⟩ := by
  simp only [killBasisRow, BinaryCoordinateSpace.mem_iff]
  decide +kernel

private theorem kill_basis_block_7 : ∀ s : Fin 8,
    ∀ hs : 8 * 7 + s.val < 1536, killBasisRow ⟨8 * 7 + s.val, hs⟩ := by
  simp only [killBasisRow, BinaryCoordinateSpace.mem_iff]
  decide +kernel

private theorem kill_basis_block_8 : ∀ s : Fin 8,
    ∀ hs : 8 * 8 + s.val < 1536, killBasisRow ⟨8 * 8 + s.val, hs⟩ := by
  simp only [killBasisRow, BinaryCoordinateSpace.mem_iff]
  decide +kernel

private theorem kill_basis_block_9 : ∀ s : Fin 8,
    ∀ hs : 8 * 9 + s.val < 1536, killBasisRow ⟨8 * 9 + s.val, hs⟩ := by
  simp only [killBasisRow, BinaryCoordinateSpace.mem_iff]
  decide +kernel

private theorem kill_basis_block_10 : ∀ s : Fin 8,
    ∀ hs : 8 * 10 + s.val < 1536, killBasisRow ⟨8 * 10 + s.val, hs⟩ := by
  simp only [killBasisRow, BinaryCoordinateSpace.mem_iff]
  decide +kernel

private theorem kill_basis_block_11 : ∀ s : Fin 8,
    ∀ hs : 8 * 11 + s.val < 1536, killBasisRow ⟨8 * 11 + s.val, hs⟩ := by
  simp only [killBasisRow, BinaryCoordinateSpace.mem_iff]
  decide +kernel

private theorem kill_basis_block_12 : ∀ s : Fin 8,
    ∀ hs : 8 * 12 + s.val < 1536, killBasisRow ⟨8 * 12 + s.val, hs⟩ := by
  simp only [killBasisRow, BinaryCoordinateSpace.mem_iff]
  decide +kernel

private theorem kill_basis_block_13 : ∀ s : Fin 8,
    ∀ hs : 8 * 13 + s.val < 1536, killBasisRow ⟨8 * 13 + s.val, hs⟩ := by
  simp only [killBasisRow, BinaryCoordinateSpace.mem_iff]
  decide +kernel

private theorem kill_basis_block_14 : ∀ s : Fin 8,
    ∀ hs : 8 * 14 + s.val < 1536, killBasisRow ⟨8 * 14 + s.val, hs⟩ := by
  simp only [killBasisRow, BinaryCoordinateSpace.mem_iff]
  decide +kernel

private theorem kill_basis_block_15 : ∀ s : Fin 8,
    ∀ hs : 8 * 15 + s.val < 1536, killBasisRow ⟨8 * 15 + s.val, hs⟩ := by
  simp only [killBasisRow, BinaryCoordinateSpace.mem_iff]
  decide +kernel

private theorem kill_basis_block_16 : ∀ s : Fin 8,
    ∀ hs : 8 * 16 + s.val < 1536, killBasisRow ⟨8 * 16 + s.val, hs⟩ := by
  simp only [killBasisRow, BinaryCoordinateSpace.mem_iff]
  decide +kernel

private theorem kill_basis_block_17 : ∀ s : Fin 8,
    ∀ hs : 8 * 17 + s.val < 1536, killBasisRow ⟨8 * 17 + s.val, hs⟩ := by
  simp only [killBasisRow, BinaryCoordinateSpace.mem_iff]
  decide +kernel

private theorem kill_basis_block_18 : ∀ s : Fin 8,
    ∀ hs : 8 * 18 + s.val < 1536, killBasisRow ⟨8 * 18 + s.val, hs⟩ := by
  simp only [killBasisRow, BinaryCoordinateSpace.mem_iff]
  decide +kernel

private theorem kill_basis_block_19 : ∀ s : Fin 8,
    ∀ hs : 8 * 19 + s.val < 1536, killBasisRow ⟨8 * 19 + s.val, hs⟩ := by
  simp only [killBasisRow, BinaryCoordinateSpace.mem_iff]
  decide +kernel

private theorem kill_basis_block_20 : ∀ s : Fin 8,
    ∀ hs : 8 * 20 + s.val < 1536, killBasisRow ⟨8 * 20 + s.val, hs⟩ := by
  simp only [killBasisRow, BinaryCoordinateSpace.mem_iff]
  decide +kernel

private theorem kill_basis_block_21 : ∀ s : Fin 8,
    ∀ hs : 8 * 21 + s.val < 1536, killBasisRow ⟨8 * 21 + s.val, hs⟩ := by
  simp only [killBasisRow, BinaryCoordinateSpace.mem_iff]
  decide +kernel

private theorem kill_basis_block_22 : ∀ s : Fin 8,
    ∀ hs : 8 * 22 + s.val < 1536, killBasisRow ⟨8 * 22 + s.val, hs⟩ := by
  simp only [killBasisRow, BinaryCoordinateSpace.mem_iff]
  decide +kernel

private theorem kill_basis_block_23 : ∀ s : Fin 8,
    ∀ hs : 8 * 23 + s.val < 1536, killBasisRow ⟨8 * 23 + s.val, hs⟩ := by
  simp only [killBasisRow, BinaryCoordinateSpace.mem_iff]
  decide +kernel

private theorem kill_basis_block_24 : ∀ s : Fin 8,
    ∀ hs : 8 * 24 + s.val < 1536, killBasisRow ⟨8 * 24 + s.val, hs⟩ := by
  simp only [killBasisRow, BinaryCoordinateSpace.mem_iff]
  decide +kernel

private theorem kill_basis_block_25 : ∀ s : Fin 8,
    ∀ hs : 8 * 25 + s.val < 1536, killBasisRow ⟨8 * 25 + s.val, hs⟩ := by
  simp only [killBasisRow, BinaryCoordinateSpace.mem_iff]
  decide +kernel

private theorem kill_basis_block_26 : ∀ s : Fin 8,
    ∀ hs : 8 * 26 + s.val < 1536, killBasisRow ⟨8 * 26 + s.val, hs⟩ := by
  simp only [killBasisRow, BinaryCoordinateSpace.mem_iff]
  decide +kernel

private theorem kill_basis_block_27 : ∀ s : Fin 8,
    ∀ hs : 8 * 27 + s.val < 1536, killBasisRow ⟨8 * 27 + s.val, hs⟩ := by
  simp only [killBasisRow, BinaryCoordinateSpace.mem_iff]
  decide +kernel

private theorem kill_basis_block_28 : ∀ s : Fin 8,
    ∀ hs : 8 * 28 + s.val < 1536, killBasisRow ⟨8 * 28 + s.val, hs⟩ := by
  simp only [killBasisRow, BinaryCoordinateSpace.mem_iff]
  decide +kernel

private theorem kill_basis_block_29 : ∀ s : Fin 8,
    ∀ hs : 8 * 29 + s.val < 1536, killBasisRow ⟨8 * 29 + s.val, hs⟩ := by
  simp only [killBasisRow, BinaryCoordinateSpace.mem_iff]
  decide +kernel

private theorem kill_basis_block_30 : ∀ s : Fin 8,
    ∀ hs : 8 * 30 + s.val < 1536, killBasisRow ⟨8 * 30 + s.val, hs⟩ := by
  simp only [killBasisRow, BinaryCoordinateSpace.mem_iff]
  decide +kernel

private theorem kill_basis_block_31 : ∀ s : Fin 8,
    ∀ hs : 8 * 31 + s.val < 1536, killBasisRow ⟨8 * 31 + s.val, hs⟩ := by
  simp only [killBasisRow, BinaryCoordinateSpace.mem_iff]
  decide +kernel

private theorem kill_basis_block_32 : ∀ s : Fin 8,
    ∀ hs : 8 * 32 + s.val < 1536, killBasisRow ⟨8 * 32 + s.val, hs⟩ := by
  simp only [killBasisRow, BinaryCoordinateSpace.mem_iff]
  decide +kernel

private theorem kill_basis_block_33 : ∀ s : Fin 8,
    ∀ hs : 8 * 33 + s.val < 1536, killBasisRow ⟨8 * 33 + s.val, hs⟩ := by
  simp only [killBasisRow, BinaryCoordinateSpace.mem_iff]
  decide +kernel

private theorem kill_basis_block_34 : ∀ s : Fin 8,
    ∀ hs : 8 * 34 + s.val < 1536, killBasisRow ⟨8 * 34 + s.val, hs⟩ := by
  simp only [killBasisRow, BinaryCoordinateSpace.mem_iff]
  decide +kernel

private theorem kill_basis_block_35 : ∀ s : Fin 8,
    ∀ hs : 8 * 35 + s.val < 1536, killBasisRow ⟨8 * 35 + s.val, hs⟩ := by
  simp only [killBasisRow, BinaryCoordinateSpace.mem_iff]
  decide +kernel

private theorem kill_basis_block_36 : ∀ s : Fin 8,
    ∀ hs : 8 * 36 + s.val < 1536, killBasisRow ⟨8 * 36 + s.val, hs⟩ := by
  simp only [killBasisRow, BinaryCoordinateSpace.mem_iff]
  decide +kernel

private theorem kill_basis_block_37 : ∀ s : Fin 8,
    ∀ hs : 8 * 37 + s.val < 1536, killBasisRow ⟨8 * 37 + s.val, hs⟩ := by
  simp only [killBasisRow, BinaryCoordinateSpace.mem_iff]
  decide +kernel

private theorem kill_basis_block_38 : ∀ s : Fin 8,
    ∀ hs : 8 * 38 + s.val < 1536, killBasisRow ⟨8 * 38 + s.val, hs⟩ := by
  simp only [killBasisRow, BinaryCoordinateSpace.mem_iff]
  decide +kernel

private theorem kill_basis_block_39 : ∀ s : Fin 8,
    ∀ hs : 8 * 39 + s.val < 1536, killBasisRow ⟨8 * 39 + s.val, hs⟩ := by
  simp only [killBasisRow, BinaryCoordinateSpace.mem_iff]
  decide +kernel

private theorem kill_basis_block_40 : ∀ s : Fin 8,
    ∀ hs : 8 * 40 + s.val < 1536, killBasisRow ⟨8 * 40 + s.val, hs⟩ := by
  simp only [killBasisRow, BinaryCoordinateSpace.mem_iff]
  decide +kernel

private theorem kill_basis_block_41 : ∀ s : Fin 8,
    ∀ hs : 8 * 41 + s.val < 1536, killBasisRow ⟨8 * 41 + s.val, hs⟩ := by
  simp only [killBasisRow, BinaryCoordinateSpace.mem_iff]
  decide +kernel

private theorem kill_basis_block_42 : ∀ s : Fin 8,
    ∀ hs : 8 * 42 + s.val < 1536, killBasisRow ⟨8 * 42 + s.val, hs⟩ := by
  simp only [killBasisRow, BinaryCoordinateSpace.mem_iff]
  decide +kernel

private theorem kill_basis_block_43 : ∀ s : Fin 8,
    ∀ hs : 8 * 43 + s.val < 1536, killBasisRow ⟨8 * 43 + s.val, hs⟩ := by
  simp only [killBasisRow, BinaryCoordinateSpace.mem_iff]
  decide +kernel

private theorem kill_basis_block_44 : ∀ s : Fin 8,
    ∀ hs : 8 * 44 + s.val < 1536, killBasisRow ⟨8 * 44 + s.val, hs⟩ := by
  simp only [killBasisRow, BinaryCoordinateSpace.mem_iff]
  decide +kernel

private theorem kill_basis_block_45 : ∀ s : Fin 8,
    ∀ hs : 8 * 45 + s.val < 1536, killBasisRow ⟨8 * 45 + s.val, hs⟩ := by
  simp only [killBasisRow, BinaryCoordinateSpace.mem_iff]
  decide +kernel

private theorem kill_basis_block_46 : ∀ s : Fin 8,
    ∀ hs : 8 * 46 + s.val < 1536, killBasisRow ⟨8 * 46 + s.val, hs⟩ := by
  simp only [killBasisRow, BinaryCoordinateSpace.mem_iff]
  decide +kernel

private theorem kill_basis_block_47 : ∀ s : Fin 8,
    ∀ hs : 8 * 47 + s.val < 1536, killBasisRow ⟨8 * 47 + s.val, hs⟩ := by
  simp only [killBasisRow, BinaryCoordinateSpace.mem_iff]
  decide +kernel

private theorem kill_basis_block_48 : ∀ s : Fin 8,
    ∀ hs : 8 * 48 + s.val < 1536, killBasisRow ⟨8 * 48 + s.val, hs⟩ := by
  simp only [killBasisRow, BinaryCoordinateSpace.mem_iff]
  decide +kernel

private theorem kill_basis_block_49 : ∀ s : Fin 8,
    ∀ hs : 8 * 49 + s.val < 1536, killBasisRow ⟨8 * 49 + s.val, hs⟩ := by
  simp only [killBasisRow, BinaryCoordinateSpace.mem_iff]
  decide +kernel

private theorem kill_basis_block_50 : ∀ s : Fin 8,
    ∀ hs : 8 * 50 + s.val < 1536, killBasisRow ⟨8 * 50 + s.val, hs⟩ := by
  simp only [killBasisRow, BinaryCoordinateSpace.mem_iff]
  decide +kernel

private theorem kill_basis_block_51 : ∀ s : Fin 8,
    ∀ hs : 8 * 51 + s.val < 1536, killBasisRow ⟨8 * 51 + s.val, hs⟩ := by
  simp only [killBasisRow, BinaryCoordinateSpace.mem_iff]
  decide +kernel

private theorem kill_basis_block_52 : ∀ s : Fin 8,
    ∀ hs : 8 * 52 + s.val < 1536, killBasisRow ⟨8 * 52 + s.val, hs⟩ := by
  simp only [killBasisRow, BinaryCoordinateSpace.mem_iff]
  decide +kernel

private theorem kill_basis_block_53 : ∀ s : Fin 8,
    ∀ hs : 8 * 53 + s.val < 1536, killBasisRow ⟨8 * 53 + s.val, hs⟩ := by
  simp only [killBasisRow, BinaryCoordinateSpace.mem_iff]
  decide +kernel

private theorem kill_basis_block_54 : ∀ s : Fin 8,
    ∀ hs : 8 * 54 + s.val < 1536, killBasisRow ⟨8 * 54 + s.val, hs⟩ := by
  simp only [killBasisRow, BinaryCoordinateSpace.mem_iff]
  decide +kernel

private theorem kill_basis_block_55 : ∀ s : Fin 8,
    ∀ hs : 8 * 55 + s.val < 1536, killBasisRow ⟨8 * 55 + s.val, hs⟩ := by
  simp only [killBasisRow, BinaryCoordinateSpace.mem_iff]
  decide +kernel

private theorem kill_basis_block_56 : ∀ s : Fin 8,
    ∀ hs : 8 * 56 + s.val < 1536, killBasisRow ⟨8 * 56 + s.val, hs⟩ := by
  simp only [killBasisRow, BinaryCoordinateSpace.mem_iff]
  decide +kernel

private theorem kill_basis_block_57 : ∀ s : Fin 8,
    ∀ hs : 8 * 57 + s.val < 1536, killBasisRow ⟨8 * 57 + s.val, hs⟩ := by
  simp only [killBasisRow, BinaryCoordinateSpace.mem_iff]
  decide +kernel

private theorem kill_basis_block_58 : ∀ s : Fin 8,
    ∀ hs : 8 * 58 + s.val < 1536, killBasisRow ⟨8 * 58 + s.val, hs⟩ := by
  simp only [killBasisRow, BinaryCoordinateSpace.mem_iff]
  decide +kernel

private theorem kill_basis_block_59 : ∀ s : Fin 8,
    ∀ hs : 8 * 59 + s.val < 1536, killBasisRow ⟨8 * 59 + s.val, hs⟩ := by
  simp only [killBasisRow, BinaryCoordinateSpace.mem_iff]
  decide +kernel

private theorem kill_basis_block_60 : ∀ s : Fin 8,
    ∀ hs : 8 * 60 + s.val < 1536, killBasisRow ⟨8 * 60 + s.val, hs⟩ := by
  simp only [killBasisRow, BinaryCoordinateSpace.mem_iff]
  decide +kernel

private theorem kill_basis_block_61 : ∀ s : Fin 8,
    ∀ hs : 8 * 61 + s.val < 1536, killBasisRow ⟨8 * 61 + s.val, hs⟩ := by
  simp only [killBasisRow, BinaryCoordinateSpace.mem_iff]
  decide +kernel

private theorem kill_basis_block_62 : ∀ s : Fin 8,
    ∀ hs : 8 * 62 + s.val < 1536, killBasisRow ⟨8 * 62 + s.val, hs⟩ := by
  simp only [killBasisRow, BinaryCoordinateSpace.mem_iff]
  decide +kernel

private theorem kill_basis_block_63 : ∀ s : Fin 8,
    ∀ hs : 8 * 63 + s.val < 1536, killBasisRow ⟨8 * 63 + s.val, hs⟩ := by
  simp only [killBasisRow, BinaryCoordinateSpace.mem_iff]
  decide +kernel

private theorem kill_basis_block_64 : ∀ s : Fin 8,
    ∀ hs : 8 * 64 + s.val < 1536, killBasisRow ⟨8 * 64 + s.val, hs⟩ := by
  simp only [killBasisRow, BinaryCoordinateSpace.mem_iff]
  decide +kernel

private theorem kill_basis_block_65 : ∀ s : Fin 8,
    ∀ hs : 8 * 65 + s.val < 1536, killBasisRow ⟨8 * 65 + s.val, hs⟩ := by
  simp only [killBasisRow, BinaryCoordinateSpace.mem_iff]
  decide +kernel

private theorem kill_basis_block_66 : ∀ s : Fin 8,
    ∀ hs : 8 * 66 + s.val < 1536, killBasisRow ⟨8 * 66 + s.val, hs⟩ := by
  simp only [killBasisRow, BinaryCoordinateSpace.mem_iff]
  decide +kernel

private theorem kill_basis_block_67 : ∀ s : Fin 8,
    ∀ hs : 8 * 67 + s.val < 1536, killBasisRow ⟨8 * 67 + s.val, hs⟩ := by
  simp only [killBasisRow, BinaryCoordinateSpace.mem_iff]
  decide +kernel

private theorem kill_basis_block_68 : ∀ s : Fin 8,
    ∀ hs : 8 * 68 + s.val < 1536, killBasisRow ⟨8 * 68 + s.val, hs⟩ := by
  simp only [killBasisRow, BinaryCoordinateSpace.mem_iff]
  decide +kernel

private theorem kill_basis_block_69 : ∀ s : Fin 8,
    ∀ hs : 8 * 69 + s.val < 1536, killBasisRow ⟨8 * 69 + s.val, hs⟩ := by
  simp only [killBasisRow, BinaryCoordinateSpace.mem_iff]
  decide +kernel

private theorem kill_basis_block_70 : ∀ s : Fin 8,
    ∀ hs : 8 * 70 + s.val < 1536, killBasisRow ⟨8 * 70 + s.val, hs⟩ := by
  simp only [killBasisRow, BinaryCoordinateSpace.mem_iff]
  decide +kernel

private theorem kill_basis_block_71 : ∀ s : Fin 8,
    ∀ hs : 8 * 71 + s.val < 1536, killBasisRow ⟨8 * 71 + s.val, hs⟩ := by
  simp only [killBasisRow, BinaryCoordinateSpace.mem_iff]
  decide +kernel

private theorem kill_basis_block_72 : ∀ s : Fin 8,
    ∀ hs : 8 * 72 + s.val < 1536, killBasisRow ⟨8 * 72 + s.val, hs⟩ := by
  simp only [killBasisRow, BinaryCoordinateSpace.mem_iff]
  decide +kernel

private theorem kill_basis_block_73 : ∀ s : Fin 8,
    ∀ hs : 8 * 73 + s.val < 1536, killBasisRow ⟨8 * 73 + s.val, hs⟩ := by
  simp only [killBasisRow, BinaryCoordinateSpace.mem_iff]
  decide +kernel

private theorem kill_basis_block_74 : ∀ s : Fin 8,
    ∀ hs : 8 * 74 + s.val < 1536, killBasisRow ⟨8 * 74 + s.val, hs⟩ := by
  simp only [killBasisRow, BinaryCoordinateSpace.mem_iff]
  decide +kernel

private theorem kill_basis_block_75 : ∀ s : Fin 8,
    ∀ hs : 8 * 75 + s.val < 1536, killBasisRow ⟨8 * 75 + s.val, hs⟩ := by
  simp only [killBasisRow, BinaryCoordinateSpace.mem_iff]
  decide +kernel

private theorem kill_basis_block_76 : ∀ s : Fin 8,
    ∀ hs : 8 * 76 + s.val < 1536, killBasisRow ⟨8 * 76 + s.val, hs⟩ := by
  simp only [killBasisRow, BinaryCoordinateSpace.mem_iff]
  decide +kernel

private theorem kill_basis_block_77 : ∀ s : Fin 8,
    ∀ hs : 8 * 77 + s.val < 1536, killBasisRow ⟨8 * 77 + s.val, hs⟩ := by
  simp only [killBasisRow, BinaryCoordinateSpace.mem_iff]
  decide +kernel

private theorem kill_basis_block_78 : ∀ s : Fin 8,
    ∀ hs : 8 * 78 + s.val < 1536, killBasisRow ⟨8 * 78 + s.val, hs⟩ := by
  simp only [killBasisRow, BinaryCoordinateSpace.mem_iff]
  decide +kernel

private theorem kill_basis_block_79 : ∀ s : Fin 8,
    ∀ hs : 8 * 79 + s.val < 1536, killBasisRow ⟨8 * 79 + s.val, hs⟩ := by
  simp only [killBasisRow, BinaryCoordinateSpace.mem_iff]
  decide +kernel

private theorem kill_basis_block_80 : ∀ s : Fin 8,
    ∀ hs : 8 * 80 + s.val < 1536, killBasisRow ⟨8 * 80 + s.val, hs⟩ := by
  simp only [killBasisRow, BinaryCoordinateSpace.mem_iff]
  decide +kernel

private theorem kill_basis_block_81 : ∀ s : Fin 8,
    ∀ hs : 8 * 81 + s.val < 1536, killBasisRow ⟨8 * 81 + s.val, hs⟩ := by
  simp only [killBasisRow, BinaryCoordinateSpace.mem_iff]
  decide +kernel

private theorem kill_basis_block_82 : ∀ s : Fin 8,
    ∀ hs : 8 * 82 + s.val < 1536, killBasisRow ⟨8 * 82 + s.val, hs⟩ := by
  simp only [killBasisRow, BinaryCoordinateSpace.mem_iff]
  decide +kernel

private theorem kill_basis_block_83 : ∀ s : Fin 8,
    ∀ hs : 8 * 83 + s.val < 1536, killBasisRow ⟨8 * 83 + s.val, hs⟩ := by
  simp only [killBasisRow, BinaryCoordinateSpace.mem_iff]
  decide +kernel

private theorem kill_basis_block_84 : ∀ s : Fin 8,
    ∀ hs : 8 * 84 + s.val < 1536, killBasisRow ⟨8 * 84 + s.val, hs⟩ := by
  simp only [killBasisRow, BinaryCoordinateSpace.mem_iff]
  decide +kernel

private theorem kill_basis_block_85 : ∀ s : Fin 8,
    ∀ hs : 8 * 85 + s.val < 1536, killBasisRow ⟨8 * 85 + s.val, hs⟩ := by
  simp only [killBasisRow, BinaryCoordinateSpace.mem_iff]
  decide +kernel

private theorem kill_basis_block_86 : ∀ s : Fin 8,
    ∀ hs : 8 * 86 + s.val < 1536, killBasisRow ⟨8 * 86 + s.val, hs⟩ := by
  simp only [killBasisRow, BinaryCoordinateSpace.mem_iff]
  decide +kernel

private theorem kill_basis_block_87 : ∀ s : Fin 8,
    ∀ hs : 8 * 87 + s.val < 1536, killBasisRow ⟨8 * 87 + s.val, hs⟩ := by
  simp only [killBasisRow, BinaryCoordinateSpace.mem_iff]
  decide +kernel

private theorem kill_basis_block_88 : ∀ s : Fin 8,
    ∀ hs : 8 * 88 + s.val < 1536, killBasisRow ⟨8 * 88 + s.val, hs⟩ := by
  simp only [killBasisRow, BinaryCoordinateSpace.mem_iff]
  decide +kernel

private theorem kill_basis_block_89 : ∀ s : Fin 8,
    ∀ hs : 8 * 89 + s.val < 1536, killBasisRow ⟨8 * 89 + s.val, hs⟩ := by
  simp only [killBasisRow, BinaryCoordinateSpace.mem_iff]
  decide +kernel

private theorem kill_basis_block_90 : ∀ s : Fin 8,
    ∀ hs : 8 * 90 + s.val < 1536, killBasisRow ⟨8 * 90 + s.val, hs⟩ := by
  simp only [killBasisRow, BinaryCoordinateSpace.mem_iff]
  decide +kernel

private theorem kill_basis_block_91 : ∀ s : Fin 8,
    ∀ hs : 8 * 91 + s.val < 1536, killBasisRow ⟨8 * 91 + s.val, hs⟩ := by
  simp only [killBasisRow, BinaryCoordinateSpace.mem_iff]
  decide +kernel

private theorem kill_basis_block_92 : ∀ s : Fin 8,
    ∀ hs : 8 * 92 + s.val < 1536, killBasisRow ⟨8 * 92 + s.val, hs⟩ := by
  simp only [killBasisRow, BinaryCoordinateSpace.mem_iff]
  decide +kernel

private theorem kill_basis_block_93 : ∀ s : Fin 8,
    ∀ hs : 8 * 93 + s.val < 1536, killBasisRow ⟨8 * 93 + s.val, hs⟩ := by
  simp only [killBasisRow, BinaryCoordinateSpace.mem_iff]
  decide +kernel

private theorem kill_basis_block_94 : ∀ s : Fin 8,
    ∀ hs : 8 * 94 + s.val < 1536, killBasisRow ⟨8 * 94 + s.val, hs⟩ := by
  simp only [killBasisRow, BinaryCoordinateSpace.mem_iff]
  decide +kernel

private theorem kill_basis_block_95 : ∀ s : Fin 8,
    ∀ hs : 8 * 95 + s.val < 1536, killBasisRow ⟨8 * 95 + s.val, hs⟩ := by
  simp only [killBasisRow, BinaryCoordinateSpace.mem_iff]
  decide +kernel

private theorem kill_basis_block_96 : ∀ s : Fin 8,
    ∀ hs : 8 * 96 + s.val < 1536, killBasisRow ⟨8 * 96 + s.val, hs⟩ := by
  simp only [killBasisRow, BinaryCoordinateSpace.mem_iff]
  decide +kernel

private theorem kill_basis_block_97 : ∀ s : Fin 8,
    ∀ hs : 8 * 97 + s.val < 1536, killBasisRow ⟨8 * 97 + s.val, hs⟩ := by
  simp only [killBasisRow, BinaryCoordinateSpace.mem_iff]
  decide +kernel

private theorem kill_basis_block_98 : ∀ s : Fin 8,
    ∀ hs : 8 * 98 + s.val < 1536, killBasisRow ⟨8 * 98 + s.val, hs⟩ := by
  simp only [killBasisRow, BinaryCoordinateSpace.mem_iff]
  decide +kernel

private theorem kill_basis_block_99 : ∀ s : Fin 8,
    ∀ hs : 8 * 99 + s.val < 1536, killBasisRow ⟨8 * 99 + s.val, hs⟩ := by
  simp only [killBasisRow, BinaryCoordinateSpace.mem_iff]
  decide +kernel

private theorem kill_basis_block_100 : ∀ s : Fin 8,
    ∀ hs : 8 * 100 + s.val < 1536, killBasisRow ⟨8 * 100 + s.val, hs⟩ := by
  simp only [killBasisRow, BinaryCoordinateSpace.mem_iff]
  decide +kernel

private theorem kill_basis_block_101 : ∀ s : Fin 8,
    ∀ hs : 8 * 101 + s.val < 1536, killBasisRow ⟨8 * 101 + s.val, hs⟩ := by
  simp only [killBasisRow, BinaryCoordinateSpace.mem_iff]
  decide +kernel

private theorem kill_basis_block_102 : ∀ s : Fin 8,
    ∀ hs : 8 * 102 + s.val < 1536, killBasisRow ⟨8 * 102 + s.val, hs⟩ := by
  simp only [killBasisRow, BinaryCoordinateSpace.mem_iff]
  decide +kernel

private theorem kill_basis_block_103 : ∀ s : Fin 8,
    ∀ hs : 8 * 103 + s.val < 1536, killBasisRow ⟨8 * 103 + s.val, hs⟩ := by
  simp only [killBasisRow, BinaryCoordinateSpace.mem_iff]
  decide +kernel

private theorem kill_basis_block_104 : ∀ s : Fin 8,
    ∀ hs : 8 * 104 + s.val < 1536, killBasisRow ⟨8 * 104 + s.val, hs⟩ := by
  simp only [killBasisRow, BinaryCoordinateSpace.mem_iff]
  decide +kernel

private theorem kill_basis_block_105 : ∀ s : Fin 8,
    ∀ hs : 8 * 105 + s.val < 1536, killBasisRow ⟨8 * 105 + s.val, hs⟩ := by
  simp only [killBasisRow, BinaryCoordinateSpace.mem_iff]
  decide +kernel

private theorem kill_basis_block_106 : ∀ s : Fin 8,
    ∀ hs : 8 * 106 + s.val < 1536, killBasisRow ⟨8 * 106 + s.val, hs⟩ := by
  simp only [killBasisRow, BinaryCoordinateSpace.mem_iff]
  decide +kernel

private theorem kill_basis_block_107 : ∀ s : Fin 8,
    ∀ hs : 8 * 107 + s.val < 1536, killBasisRow ⟨8 * 107 + s.val, hs⟩ := by
  simp only [killBasisRow, BinaryCoordinateSpace.mem_iff]
  decide +kernel

private theorem kill_basis_block_108 : ∀ s : Fin 8,
    ∀ hs : 8 * 108 + s.val < 1536, killBasisRow ⟨8 * 108 + s.val, hs⟩ := by
  simp only [killBasisRow, BinaryCoordinateSpace.mem_iff]
  decide +kernel

private theorem kill_basis_block_109 : ∀ s : Fin 8,
    ∀ hs : 8 * 109 + s.val < 1536, killBasisRow ⟨8 * 109 + s.val, hs⟩ := by
  simp only [killBasisRow, BinaryCoordinateSpace.mem_iff]
  decide +kernel

private theorem kill_basis_block_110 : ∀ s : Fin 8,
    ∀ hs : 8 * 110 + s.val < 1536, killBasisRow ⟨8 * 110 + s.val, hs⟩ := by
  simp only [killBasisRow, BinaryCoordinateSpace.mem_iff]
  decide +kernel

private theorem kill_basis_block_111 : ∀ s : Fin 8,
    ∀ hs : 8 * 111 + s.val < 1536, killBasisRow ⟨8 * 111 + s.val, hs⟩ := by
  simp only [killBasisRow, BinaryCoordinateSpace.mem_iff]
  decide +kernel

private theorem kill_basis_block_112 : ∀ s : Fin 8,
    ∀ hs : 8 * 112 + s.val < 1536, killBasisRow ⟨8 * 112 + s.val, hs⟩ := by
  simp only [killBasisRow, BinaryCoordinateSpace.mem_iff]
  decide +kernel

private theorem kill_basis_block_113 : ∀ s : Fin 8,
    ∀ hs : 8 * 113 + s.val < 1536, killBasisRow ⟨8 * 113 + s.val, hs⟩ := by
  simp only [killBasisRow, BinaryCoordinateSpace.mem_iff]
  decide +kernel

private theorem kill_basis_block_114 : ∀ s : Fin 8,
    ∀ hs : 8 * 114 + s.val < 1536, killBasisRow ⟨8 * 114 + s.val, hs⟩ := by
  simp only [killBasisRow, BinaryCoordinateSpace.mem_iff]
  decide +kernel

private theorem kill_basis_block_115 : ∀ s : Fin 8,
    ∀ hs : 8 * 115 + s.val < 1536, killBasisRow ⟨8 * 115 + s.val, hs⟩ := by
  simp only [killBasisRow, BinaryCoordinateSpace.mem_iff]
  decide +kernel

private theorem kill_basis_block_116 : ∀ s : Fin 8,
    ∀ hs : 8 * 116 + s.val < 1536, killBasisRow ⟨8 * 116 + s.val, hs⟩ := by
  simp only [killBasisRow, BinaryCoordinateSpace.mem_iff]
  decide +kernel

private theorem kill_basis_block_117 : ∀ s : Fin 8,
    ∀ hs : 8 * 117 + s.val < 1536, killBasisRow ⟨8 * 117 + s.val, hs⟩ := by
  simp only [killBasisRow, BinaryCoordinateSpace.mem_iff]
  decide +kernel

private theorem kill_basis_block_118 : ∀ s : Fin 8,
    ∀ hs : 8 * 118 + s.val < 1536, killBasisRow ⟨8 * 118 + s.val, hs⟩ := by
  simp only [killBasisRow, BinaryCoordinateSpace.mem_iff]
  decide +kernel

private theorem kill_basis_block_119 : ∀ s : Fin 8,
    ∀ hs : 8 * 119 + s.val < 1536, killBasisRow ⟨8 * 119 + s.val, hs⟩ := by
  simp only [killBasisRow, BinaryCoordinateSpace.mem_iff]
  decide +kernel

private theorem kill_basis_block_120 : ∀ s : Fin 8,
    ∀ hs : 8 * 120 + s.val < 1536, killBasisRow ⟨8 * 120 + s.val, hs⟩ := by
  simp only [killBasisRow, BinaryCoordinateSpace.mem_iff]
  decide +kernel

private theorem kill_basis_block_121 : ∀ s : Fin 8,
    ∀ hs : 8 * 121 + s.val < 1536, killBasisRow ⟨8 * 121 + s.val, hs⟩ := by
  simp only [killBasisRow, BinaryCoordinateSpace.mem_iff]
  decide +kernel

private theorem kill_basis_block_122 : ∀ s : Fin 8,
    ∀ hs : 8 * 122 + s.val < 1536, killBasisRow ⟨8 * 122 + s.val, hs⟩ := by
  simp only [killBasisRow, BinaryCoordinateSpace.mem_iff]
  decide +kernel

private theorem kill_basis_block_123 : ∀ s : Fin 8,
    ∀ hs : 8 * 123 + s.val < 1536, killBasisRow ⟨8 * 123 + s.val, hs⟩ := by
  simp only [killBasisRow, BinaryCoordinateSpace.mem_iff]
  decide +kernel

private theorem kill_basis_block_124 : ∀ s : Fin 8,
    ∀ hs : 8 * 124 + s.val < 1536, killBasisRow ⟨8 * 124 + s.val, hs⟩ := by
  simp only [killBasisRow, BinaryCoordinateSpace.mem_iff]
  decide +kernel

private theorem kill_basis_block_125 : ∀ s : Fin 8,
    ∀ hs : 8 * 125 + s.val < 1536, killBasisRow ⟨8 * 125 + s.val, hs⟩ := by
  simp only [killBasisRow, BinaryCoordinateSpace.mem_iff]
  decide +kernel

private theorem kill_basis_block_126 : ∀ s : Fin 8,
    ∀ hs : 8 * 126 + s.val < 1536, killBasisRow ⟨8 * 126 + s.val, hs⟩ := by
  simp only [killBasisRow, BinaryCoordinateSpace.mem_iff]
  decide +kernel

private theorem kill_basis_block_127 : ∀ s : Fin 8,
    ∀ hs : 8 * 127 + s.val < 1536, killBasisRow ⟨8 * 127 + s.val, hs⟩ := by
  simp only [killBasisRow, BinaryCoordinateSpace.mem_iff]
  decide +kernel

private theorem kill_basis_block_128 : ∀ s : Fin 8,
    ∀ hs : 8 * 128 + s.val < 1536, killBasisRow ⟨8 * 128 + s.val, hs⟩ := by
  simp only [killBasisRow, BinaryCoordinateSpace.mem_iff]
  decide +kernel

private theorem kill_basis_block_129 : ∀ s : Fin 8,
    ∀ hs : 8 * 129 + s.val < 1536, killBasisRow ⟨8 * 129 + s.val, hs⟩ := by
  simp only [killBasisRow, BinaryCoordinateSpace.mem_iff]
  decide +kernel

private theorem kill_basis_block_130 : ∀ s : Fin 8,
    ∀ hs : 8 * 130 + s.val < 1536, killBasisRow ⟨8 * 130 + s.val, hs⟩ := by
  simp only [killBasisRow, BinaryCoordinateSpace.mem_iff]
  decide +kernel

private theorem kill_basis_block_131 : ∀ s : Fin 8,
    ∀ hs : 8 * 131 + s.val < 1536, killBasisRow ⟨8 * 131 + s.val, hs⟩ := by
  simp only [killBasisRow, BinaryCoordinateSpace.mem_iff]
  decide +kernel

private theorem kill_basis_block_132 : ∀ s : Fin 8,
    ∀ hs : 8 * 132 + s.val < 1536, killBasisRow ⟨8 * 132 + s.val, hs⟩ := by
  simp only [killBasisRow, BinaryCoordinateSpace.mem_iff]
  decide +kernel

private theorem kill_basis_block_133 : ∀ s : Fin 8,
    ∀ hs : 8 * 133 + s.val < 1536, killBasisRow ⟨8 * 133 + s.val, hs⟩ := by
  simp only [killBasisRow, BinaryCoordinateSpace.mem_iff]
  decide +kernel

private theorem kill_basis_block_134 : ∀ s : Fin 8,
    ∀ hs : 8 * 134 + s.val < 1536, killBasisRow ⟨8 * 134 + s.val, hs⟩ := by
  simp only [killBasisRow, BinaryCoordinateSpace.mem_iff]
  decide +kernel

private theorem kill_basis_block_135 : ∀ s : Fin 8,
    ∀ hs : 8 * 135 + s.val < 1536, killBasisRow ⟨8 * 135 + s.val, hs⟩ := by
  simp only [killBasisRow, BinaryCoordinateSpace.mem_iff]
  decide +kernel

private theorem kill_basis_block_136 : ∀ s : Fin 8,
    ∀ hs : 8 * 136 + s.val < 1536, killBasisRow ⟨8 * 136 + s.val, hs⟩ := by
  simp only [killBasisRow, BinaryCoordinateSpace.mem_iff]
  decide +kernel

private theorem kill_basis_block_137 : ∀ s : Fin 8,
    ∀ hs : 8 * 137 + s.val < 1536, killBasisRow ⟨8 * 137 + s.val, hs⟩ := by
  simp only [killBasisRow, BinaryCoordinateSpace.mem_iff]
  decide +kernel

private theorem kill_basis_block_138 : ∀ s : Fin 8,
    ∀ hs : 8 * 138 + s.val < 1536, killBasisRow ⟨8 * 138 + s.val, hs⟩ := by
  simp only [killBasisRow, BinaryCoordinateSpace.mem_iff]
  decide +kernel

private theorem kill_basis_block_139 : ∀ s : Fin 8,
    ∀ hs : 8 * 139 + s.val < 1536, killBasisRow ⟨8 * 139 + s.val, hs⟩ := by
  simp only [killBasisRow, BinaryCoordinateSpace.mem_iff]
  decide +kernel

private theorem kill_basis_block_140 : ∀ s : Fin 8,
    ∀ hs : 8 * 140 + s.val < 1536, killBasisRow ⟨8 * 140 + s.val, hs⟩ := by
  simp only [killBasisRow, BinaryCoordinateSpace.mem_iff]
  decide +kernel

private theorem kill_basis_block_141 : ∀ s : Fin 8,
    ∀ hs : 8 * 141 + s.val < 1536, killBasisRow ⟨8 * 141 + s.val, hs⟩ := by
  simp only [killBasisRow, BinaryCoordinateSpace.mem_iff]
  decide +kernel

private theorem kill_basis_block_142 : ∀ s : Fin 8,
    ∀ hs : 8 * 142 + s.val < 1536, killBasisRow ⟨8 * 142 + s.val, hs⟩ := by
  simp only [killBasisRow, BinaryCoordinateSpace.mem_iff]
  decide +kernel

private theorem kill_basis_block_143 : ∀ s : Fin 8,
    ∀ hs : 8 * 143 + s.val < 1536, killBasisRow ⟨8 * 143 + s.val, hs⟩ := by
  simp only [killBasisRow, BinaryCoordinateSpace.mem_iff]
  decide +kernel

private theorem kill_basis_block_144 : ∀ s : Fin 8,
    ∀ hs : 8 * 144 + s.val < 1536, killBasisRow ⟨8 * 144 + s.val, hs⟩ := by
  simp only [killBasisRow, BinaryCoordinateSpace.mem_iff]
  decide +kernel

private theorem kill_basis_block_145 : ∀ s : Fin 8,
    ∀ hs : 8 * 145 + s.val < 1536, killBasisRow ⟨8 * 145 + s.val, hs⟩ := by
  simp only [killBasisRow, BinaryCoordinateSpace.mem_iff]
  decide +kernel

private theorem kill_basis_block_146 : ∀ s : Fin 8,
    ∀ hs : 8 * 146 + s.val < 1536, killBasisRow ⟨8 * 146 + s.val, hs⟩ := by
  simp only [killBasisRow, BinaryCoordinateSpace.mem_iff]
  decide +kernel

private theorem kill_basis_block_147 : ∀ s : Fin 8,
    ∀ hs : 8 * 147 + s.val < 1536, killBasisRow ⟨8 * 147 + s.val, hs⟩ := by
  simp only [killBasisRow, BinaryCoordinateSpace.mem_iff]
  decide +kernel

private theorem kill_basis_block_148 : ∀ s : Fin 8,
    ∀ hs : 8 * 148 + s.val < 1536, killBasisRow ⟨8 * 148 + s.val, hs⟩ := by
  simp only [killBasisRow, BinaryCoordinateSpace.mem_iff]
  decide +kernel

private theorem kill_basis_block_149 : ∀ s : Fin 8,
    ∀ hs : 8 * 149 + s.val < 1536, killBasisRow ⟨8 * 149 + s.val, hs⟩ := by
  simp only [killBasisRow, BinaryCoordinateSpace.mem_iff]
  decide +kernel

private theorem kill_basis_block_150 : ∀ s : Fin 8,
    ∀ hs : 8 * 150 + s.val < 1536, killBasisRow ⟨8 * 150 + s.val, hs⟩ := by
  simp only [killBasisRow, BinaryCoordinateSpace.mem_iff]
  decide +kernel

private theorem kill_basis_block_151 : ∀ s : Fin 8,
    ∀ hs : 8 * 151 + s.val < 1536, killBasisRow ⟨8 * 151 + s.val, hs⟩ := by
  simp only [killBasisRow, BinaryCoordinateSpace.mem_iff]
  decide +kernel

private theorem kill_basis_block_152 : ∀ s : Fin 8,
    ∀ hs : 8 * 152 + s.val < 1536, killBasisRow ⟨8 * 152 + s.val, hs⟩ := by
  simp only [killBasisRow, BinaryCoordinateSpace.mem_iff]
  decide +kernel

private theorem kill_basis_block_153 : ∀ s : Fin 8,
    ∀ hs : 8 * 153 + s.val < 1536, killBasisRow ⟨8 * 153 + s.val, hs⟩ := by
  simp only [killBasisRow, BinaryCoordinateSpace.mem_iff]
  decide +kernel

private theorem kill_basis_block_154 : ∀ s : Fin 8,
    ∀ hs : 8 * 154 + s.val < 1536, killBasisRow ⟨8 * 154 + s.val, hs⟩ := by
  simp only [killBasisRow, BinaryCoordinateSpace.mem_iff]
  decide +kernel

private theorem kill_basis_block_155 : ∀ s : Fin 8,
    ∀ hs : 8 * 155 + s.val < 1536, killBasisRow ⟨8 * 155 + s.val, hs⟩ := by
  simp only [killBasisRow, BinaryCoordinateSpace.mem_iff]
  decide +kernel

private theorem kill_basis_block_156 : ∀ s : Fin 8,
    ∀ hs : 8 * 156 + s.val < 1536, killBasisRow ⟨8 * 156 + s.val, hs⟩ := by
  simp only [killBasisRow, BinaryCoordinateSpace.mem_iff]
  decide +kernel

private theorem kill_basis_block_157 : ∀ s : Fin 8,
    ∀ hs : 8 * 157 + s.val < 1536, killBasisRow ⟨8 * 157 + s.val, hs⟩ := by
  simp only [killBasisRow, BinaryCoordinateSpace.mem_iff]
  decide +kernel

private theorem kill_basis_block_158 : ∀ s : Fin 8,
    ∀ hs : 8 * 158 + s.val < 1536, killBasisRow ⟨8 * 158 + s.val, hs⟩ := by
  simp only [killBasisRow, BinaryCoordinateSpace.mem_iff]
  decide +kernel

private theorem kill_basis_block_159 : ∀ s : Fin 8,
    ∀ hs : 8 * 159 + s.val < 1536, killBasisRow ⟨8 * 159 + s.val, hs⟩ := by
  simp only [killBasisRow, BinaryCoordinateSpace.mem_iff]
  decide +kernel

private theorem kill_basis_block_160 : ∀ s : Fin 8,
    ∀ hs : 8 * 160 + s.val < 1536, killBasisRow ⟨8 * 160 + s.val, hs⟩ := by
  simp only [killBasisRow, BinaryCoordinateSpace.mem_iff]
  decide +kernel

private theorem kill_basis_block_161 : ∀ s : Fin 8,
    ∀ hs : 8 * 161 + s.val < 1536, killBasisRow ⟨8 * 161 + s.val, hs⟩ := by
  simp only [killBasisRow, BinaryCoordinateSpace.mem_iff]
  decide +kernel

private theorem kill_basis_block_162 : ∀ s : Fin 8,
    ∀ hs : 8 * 162 + s.val < 1536, killBasisRow ⟨8 * 162 + s.val, hs⟩ := by
  simp only [killBasisRow, BinaryCoordinateSpace.mem_iff]
  decide +kernel

private theorem kill_basis_block_163 : ∀ s : Fin 8,
    ∀ hs : 8 * 163 + s.val < 1536, killBasisRow ⟨8 * 163 + s.val, hs⟩ := by
  simp only [killBasisRow, BinaryCoordinateSpace.mem_iff]
  decide +kernel

private theorem kill_basis_block_164 : ∀ s : Fin 8,
    ∀ hs : 8 * 164 + s.val < 1536, killBasisRow ⟨8 * 164 + s.val, hs⟩ := by
  simp only [killBasisRow, BinaryCoordinateSpace.mem_iff]
  decide +kernel

private theorem kill_basis_block_165 : ∀ s : Fin 8,
    ∀ hs : 8 * 165 + s.val < 1536, killBasisRow ⟨8 * 165 + s.val, hs⟩ := by
  simp only [killBasisRow, BinaryCoordinateSpace.mem_iff]
  decide +kernel

private theorem kill_basis_block_166 : ∀ s : Fin 8,
    ∀ hs : 8 * 166 + s.val < 1536, killBasisRow ⟨8 * 166 + s.val, hs⟩ := by
  simp only [killBasisRow, BinaryCoordinateSpace.mem_iff]
  decide +kernel

private theorem kill_basis_block_167 : ∀ s : Fin 8,
    ∀ hs : 8 * 167 + s.val < 1536, killBasisRow ⟨8 * 167 + s.val, hs⟩ := by
  simp only [killBasisRow, BinaryCoordinateSpace.mem_iff]
  decide +kernel

private theorem kill_basis_block_168 : ∀ s : Fin 8,
    ∀ hs : 8 * 168 + s.val < 1536, killBasisRow ⟨8 * 168 + s.val, hs⟩ := by
  simp only [killBasisRow, BinaryCoordinateSpace.mem_iff]
  decide +kernel

private theorem kill_basis_block_169 : ∀ s : Fin 8,
    ∀ hs : 8 * 169 + s.val < 1536, killBasisRow ⟨8 * 169 + s.val, hs⟩ := by
  simp only [killBasisRow, BinaryCoordinateSpace.mem_iff]
  decide +kernel

private theorem kill_basis_block_170 : ∀ s : Fin 8,
    ∀ hs : 8 * 170 + s.val < 1536, killBasisRow ⟨8 * 170 + s.val, hs⟩ := by
  simp only [killBasisRow, BinaryCoordinateSpace.mem_iff]
  decide +kernel

private theorem kill_basis_block_171 : ∀ s : Fin 8,
    ∀ hs : 8 * 171 + s.val < 1536, killBasisRow ⟨8 * 171 + s.val, hs⟩ := by
  simp only [killBasisRow, BinaryCoordinateSpace.mem_iff]
  decide +kernel

private theorem kill_basis_block_172 : ∀ s : Fin 8,
    ∀ hs : 8 * 172 + s.val < 1536, killBasisRow ⟨8 * 172 + s.val, hs⟩ := by
  simp only [killBasisRow, BinaryCoordinateSpace.mem_iff]
  decide +kernel

private theorem kill_basis_block_173 : ∀ s : Fin 8,
    ∀ hs : 8 * 173 + s.val < 1536, killBasisRow ⟨8 * 173 + s.val, hs⟩ := by
  simp only [killBasisRow, BinaryCoordinateSpace.mem_iff]
  decide +kernel

private theorem kill_basis_block_174 : ∀ s : Fin 8,
    ∀ hs : 8 * 174 + s.val < 1536, killBasisRow ⟨8 * 174 + s.val, hs⟩ := by
  simp only [killBasisRow, BinaryCoordinateSpace.mem_iff]
  decide +kernel

private theorem kill_basis_block_175 : ∀ s : Fin 8,
    ∀ hs : 8 * 175 + s.val < 1536, killBasisRow ⟨8 * 175 + s.val, hs⟩ := by
  simp only [killBasisRow, BinaryCoordinateSpace.mem_iff]
  decide +kernel

private theorem kill_basis_block_176 : ∀ s : Fin 8,
    ∀ hs : 8 * 176 + s.val < 1536, killBasisRow ⟨8 * 176 + s.val, hs⟩ := by
  simp only [killBasisRow, BinaryCoordinateSpace.mem_iff]
  decide +kernel

private theorem kill_basis_block_177 : ∀ s : Fin 8,
    ∀ hs : 8 * 177 + s.val < 1536, killBasisRow ⟨8 * 177 + s.val, hs⟩ := by
  simp only [killBasisRow, BinaryCoordinateSpace.mem_iff]
  decide +kernel

private theorem kill_basis_block_178 : ∀ s : Fin 8,
    ∀ hs : 8 * 178 + s.val < 1536, killBasisRow ⟨8 * 178 + s.val, hs⟩ := by
  simp only [killBasisRow, BinaryCoordinateSpace.mem_iff]
  decide +kernel

private theorem kill_basis_block_179 : ∀ s : Fin 8,
    ∀ hs : 8 * 179 + s.val < 1536, killBasisRow ⟨8 * 179 + s.val, hs⟩ := by
  simp only [killBasisRow, BinaryCoordinateSpace.mem_iff]
  decide +kernel

private theorem kill_basis_block_180 : ∀ s : Fin 8,
    ∀ hs : 8 * 180 + s.val < 1536, killBasisRow ⟨8 * 180 + s.val, hs⟩ := by
  simp only [killBasisRow, BinaryCoordinateSpace.mem_iff]
  decide +kernel

private theorem kill_basis_block_181 : ∀ s : Fin 8,
    ∀ hs : 8 * 181 + s.val < 1536, killBasisRow ⟨8 * 181 + s.val, hs⟩ := by
  simp only [killBasisRow, BinaryCoordinateSpace.mem_iff]
  decide +kernel

private theorem kill_basis_block_182 : ∀ s : Fin 8,
    ∀ hs : 8 * 182 + s.val < 1536, killBasisRow ⟨8 * 182 + s.val, hs⟩ := by
  simp only [killBasisRow, BinaryCoordinateSpace.mem_iff]
  decide +kernel

private theorem kill_basis_block_183 : ∀ s : Fin 8,
    ∀ hs : 8 * 183 + s.val < 1536, killBasisRow ⟨8 * 183 + s.val, hs⟩ := by
  simp only [killBasisRow, BinaryCoordinateSpace.mem_iff]
  decide +kernel

private theorem kill_basis_block_184 : ∀ s : Fin 8,
    ∀ hs : 8 * 184 + s.val < 1536, killBasisRow ⟨8 * 184 + s.val, hs⟩ := by
  simp only [killBasisRow, BinaryCoordinateSpace.mem_iff]
  decide +kernel

private theorem kill_basis_block_185 : ∀ s : Fin 8,
    ∀ hs : 8 * 185 + s.val < 1536, killBasisRow ⟨8 * 185 + s.val, hs⟩ := by
  simp only [killBasisRow, BinaryCoordinateSpace.mem_iff]
  decide +kernel

private theorem kill_basis_block_186 : ∀ s : Fin 8,
    ∀ hs : 8 * 186 + s.val < 1536, killBasisRow ⟨8 * 186 + s.val, hs⟩ := by
  simp only [killBasisRow, BinaryCoordinateSpace.mem_iff]
  decide +kernel

private theorem kill_basis_block_187 : ∀ s : Fin 8,
    ∀ hs : 8 * 187 + s.val < 1536, killBasisRow ⟨8 * 187 + s.val, hs⟩ := by
  simp only [killBasisRow, BinaryCoordinateSpace.mem_iff]
  decide +kernel

private theorem kill_basis_block_188 : ∀ s : Fin 8,
    ∀ hs : 8 * 188 + s.val < 1536, killBasisRow ⟨8 * 188 + s.val, hs⟩ := by
  simp only [killBasisRow, BinaryCoordinateSpace.mem_iff]
  decide +kernel

private theorem kill_basis_block_189 : ∀ s : Fin 8,
    ∀ hs : 8 * 189 + s.val < 1536, killBasisRow ⟨8 * 189 + s.val, hs⟩ := by
  simp only [killBasisRow, BinaryCoordinateSpace.mem_iff]
  decide +kernel

private theorem kill_basis_block_190 : ∀ s : Fin 8,
    ∀ hs : 8 * 190 + s.val < 1536, killBasisRow ⟨8 * 190 + s.val, hs⟩ := by
  simp only [killBasisRow, BinaryCoordinateSpace.mem_iff]
  decide +kernel

private theorem kill_basis_block_191 : ∀ s : Fin 8,
    ∀ hs : 8 * 191 + s.val < 1536, killBasisRow ⟨8 * 191 + s.val, hs⟩ := by
  simp only [killBasisRow, BinaryCoordinateSpace.mem_iff]
  decide +kernel

private theorem kill_basis_rows (n : Fin 1536) : killBasisRow n := by
  apply FiniteEightRowSlices.apply killBasisRow
  intro q
  fin_cases q

  · exact kill_basis_block_0

  · exact kill_basis_block_1

  · exact kill_basis_block_2

  · exact kill_basis_block_3

  · exact kill_basis_block_4

  · exact kill_basis_block_5

  · exact kill_basis_block_6

  · exact kill_basis_block_7

  · exact kill_basis_block_8

  · exact kill_basis_block_9

  · exact kill_basis_block_10

  · exact kill_basis_block_11

  · exact kill_basis_block_12

  · exact kill_basis_block_13

  · exact kill_basis_block_14

  · exact kill_basis_block_15

  · exact kill_basis_block_16

  · exact kill_basis_block_17

  · exact kill_basis_block_18

  · exact kill_basis_block_19

  · exact kill_basis_block_20

  · exact kill_basis_block_21

  · exact kill_basis_block_22

  · exact kill_basis_block_23

  · exact kill_basis_block_24

  · exact kill_basis_block_25

  · exact kill_basis_block_26

  · exact kill_basis_block_27

  · exact kill_basis_block_28

  · exact kill_basis_block_29

  · exact kill_basis_block_30

  · exact kill_basis_block_31

  · exact kill_basis_block_32

  · exact kill_basis_block_33

  · exact kill_basis_block_34

  · exact kill_basis_block_35

  · exact kill_basis_block_36

  · exact kill_basis_block_37

  · exact kill_basis_block_38

  · exact kill_basis_block_39

  · exact kill_basis_block_40

  · exact kill_basis_block_41

  · exact kill_basis_block_42

  · exact kill_basis_block_43

  · exact kill_basis_block_44

  · exact kill_basis_block_45

  · exact kill_basis_block_46

  · exact kill_basis_block_47

  · exact kill_basis_block_48

  · exact kill_basis_block_49

  · exact kill_basis_block_50

  · exact kill_basis_block_51

  · exact kill_basis_block_52

  · exact kill_basis_block_53

  · exact kill_basis_block_54

  · exact kill_basis_block_55

  · exact kill_basis_block_56

  · exact kill_basis_block_57

  · exact kill_basis_block_58

  · exact kill_basis_block_59

  · exact kill_basis_block_60

  · exact kill_basis_block_61

  · exact kill_basis_block_62

  · exact kill_basis_block_63

  · exact kill_basis_block_64

  · exact kill_basis_block_65

  · exact kill_basis_block_66

  · exact kill_basis_block_67

  · exact kill_basis_block_68

  · exact kill_basis_block_69

  · exact kill_basis_block_70

  · exact kill_basis_block_71

  · exact kill_basis_block_72

  · exact kill_basis_block_73

  · exact kill_basis_block_74

  · exact kill_basis_block_75

  · exact kill_basis_block_76

  · exact kill_basis_block_77

  · exact kill_basis_block_78

  · exact kill_basis_block_79

  · exact kill_basis_block_80

  · exact kill_basis_block_81

  · exact kill_basis_block_82

  · exact kill_basis_block_83

  · exact kill_basis_block_84

  · exact kill_basis_block_85

  · exact kill_basis_block_86

  · exact kill_basis_block_87

  · exact kill_basis_block_88

  · exact kill_basis_block_89

  · exact kill_basis_block_90

  · exact kill_basis_block_91

  · exact kill_basis_block_92

  · exact kill_basis_block_93

  · exact kill_basis_block_94

  · exact kill_basis_block_95

  · exact kill_basis_block_96

  · exact kill_basis_block_97

  · exact kill_basis_block_98

  · exact kill_basis_block_99

  · exact kill_basis_block_100

  · exact kill_basis_block_101

  · exact kill_basis_block_102

  · exact kill_basis_block_103

  · exact kill_basis_block_104

  · exact kill_basis_block_105

  · exact kill_basis_block_106

  · exact kill_basis_block_107

  · exact kill_basis_block_108

  · exact kill_basis_block_109

  · exact kill_basis_block_110

  · exact kill_basis_block_111

  · exact kill_basis_block_112

  · exact kill_basis_block_113

  · exact kill_basis_block_114

  · exact kill_basis_block_115

  · exact kill_basis_block_116

  · exact kill_basis_block_117

  · exact kill_basis_block_118

  · exact kill_basis_block_119

  · exact kill_basis_block_120

  · exact kill_basis_block_121

  · exact kill_basis_block_122

  · exact kill_basis_block_123

  · exact kill_basis_block_124

  · exact kill_basis_block_125

  · exact kill_basis_block_126

  · exact kill_basis_block_127

  · exact kill_basis_block_128

  · exact kill_basis_block_129

  · exact kill_basis_block_130

  · exact kill_basis_block_131

  · exact kill_basis_block_132

  · exact kill_basis_block_133

  · exact kill_basis_block_134

  · exact kill_basis_block_135

  · exact kill_basis_block_136

  · exact kill_basis_block_137

  · exact kill_basis_block_138

  · exact kill_basis_block_139

  · exact kill_basis_block_140

  · exact kill_basis_block_141

  · exact kill_basis_block_142

  · exact kill_basis_block_143

  · exact kill_basis_block_144

  · exact kill_basis_block_145

  · exact kill_basis_block_146

  · exact kill_basis_block_147

  · exact kill_basis_block_148

  · exact kill_basis_block_149

  · exact kill_basis_block_150

  · exact kill_basis_block_151

  · exact kill_basis_block_152

  · exact kill_basis_block_153

  · exact kill_basis_block_154

  · exact kill_basis_block_155

  · exact kill_basis_block_156

  · exact kill_basis_block_157

  · exact kill_basis_block_158

  · exact kill_basis_block_159

  · exact kill_basis_block_160

  · exact kill_basis_block_161

  · exact kill_basis_block_162

  · exact kill_basis_block_163

  · exact kill_basis_block_164

  · exact kill_basis_block_165

  · exact kill_basis_block_166

  · exact kill_basis_block_167

  · exact kill_basis_block_168

  · exact kill_basis_block_169

  · exact kill_basis_block_170

  · exact kill_basis_block_171

  · exact kill_basis_block_172

  · exact kill_basis_block_173

  · exact kill_basis_block_174

  · exact kill_basis_block_175

  · exact kill_basis_block_176

  · exact kill_basis_block_177

  · exact kill_basis_block_178

  · exact kill_basis_block_179

  · exact kill_basis_block_180

  · exact kill_basis_block_181

  · exact kill_basis_block_182

  · exact kill_basis_block_183

  · exact kill_basis_block_184

  · exact kill_basis_block_185

  · exact kill_basis_block_186

  · exact kill_basis_block_187

  · exact kill_basis_block_188

  · exact kill_basis_block_189

  · exact kill_basis_block_190

  · exact kill_basis_block_191

theorem kill_basis (i : Fin 128) (j : Fin 12) :
    rowAction i (state.inclusion (Pi.single j 1)) - state.inclusion (Pi.single j 1) ∈ radical.space := by
  have h := kill_basis_rows (finProdFinEquiv (i, j))
  simpa only [killBasisRow, Equiv.symm_apply_apply] using h
private theorem quotient_coordinates_surjective :
    Function.Surjective (fun n : Fin 16 => binaryVectorOfMask 4 n.val) := by
  change ∀ c : Fin 4 → ZMod 2, ∃ n : Fin 16, binaryVectorOfMask 4 n.val = c
  decide +kernel

private theorem section_count_row_0 : binaryVectorOfMask 4 0 ≠ 0 →
    Nat.card {i : Fin 128 // rowAction i (sectionMap (binaryVectorOfMask 4 0)) -
      sectionMap (binaryVectorOfMask 4 0) ∈ radical.space} ≤ 16 := by
  simp only [BinaryCoordinateSpace.mem_iff, Nat.card_eq_fintype_card]
  decide +kernel

private theorem section_count_row_1 : binaryVectorOfMask 4 1 ≠ 0 →
    Nat.card {i : Fin 128 // rowAction i (sectionMap (binaryVectorOfMask 4 1)) -
      sectionMap (binaryVectorOfMask 4 1) ∈ radical.space} ≤ 16 := by
  simp only [BinaryCoordinateSpace.mem_iff, Nat.card_eq_fintype_card]
  decide +kernel

private theorem section_count_row_2 : binaryVectorOfMask 4 2 ≠ 0 →
    Nat.card {i : Fin 128 // rowAction i (sectionMap (binaryVectorOfMask 4 2)) -
      sectionMap (binaryVectorOfMask 4 2) ∈ radical.space} ≤ 16 := by
  simp only [BinaryCoordinateSpace.mem_iff, Nat.card_eq_fintype_card]
  decide +kernel

private theorem section_count_row_3 : binaryVectorOfMask 4 3 ≠ 0 →
    Nat.card {i : Fin 128 // rowAction i (sectionMap (binaryVectorOfMask 4 3)) -
      sectionMap (binaryVectorOfMask 4 3) ∈ radical.space} ≤ 16 := by
  simp only [BinaryCoordinateSpace.mem_iff, Nat.card_eq_fintype_card]
  decide +kernel

private theorem section_count_row_4 : binaryVectorOfMask 4 4 ≠ 0 →
    Nat.card {i : Fin 128 // rowAction i (sectionMap (binaryVectorOfMask 4 4)) -
      sectionMap (binaryVectorOfMask 4 4) ∈ radical.space} ≤ 16 := by
  simp only [BinaryCoordinateSpace.mem_iff, Nat.card_eq_fintype_card]
  decide +kernel

private theorem section_count_row_5 : binaryVectorOfMask 4 5 ≠ 0 →
    Nat.card {i : Fin 128 // rowAction i (sectionMap (binaryVectorOfMask 4 5)) -
      sectionMap (binaryVectorOfMask 4 5) ∈ radical.space} ≤ 16 := by
  simp only [BinaryCoordinateSpace.mem_iff, Nat.card_eq_fintype_card]
  decide +kernel

private theorem section_count_row_6 : binaryVectorOfMask 4 6 ≠ 0 →
    Nat.card {i : Fin 128 // rowAction i (sectionMap (binaryVectorOfMask 4 6)) -
      sectionMap (binaryVectorOfMask 4 6) ∈ radical.space} ≤ 16 := by
  simp only [BinaryCoordinateSpace.mem_iff, Nat.card_eq_fintype_card]
  decide +kernel

private theorem section_count_row_7 : binaryVectorOfMask 4 7 ≠ 0 →
    Nat.card {i : Fin 128 // rowAction i (sectionMap (binaryVectorOfMask 4 7)) -
      sectionMap (binaryVectorOfMask 4 7) ∈ radical.space} ≤ 16 := by
  simp only [BinaryCoordinateSpace.mem_iff, Nat.card_eq_fintype_card]
  decide +kernel

private theorem section_count_row_8 : binaryVectorOfMask 4 8 ≠ 0 →
    Nat.card {i : Fin 128 // rowAction i (sectionMap (binaryVectorOfMask 4 8)) -
      sectionMap (binaryVectorOfMask 4 8) ∈ radical.space} ≤ 16 := by
  simp only [BinaryCoordinateSpace.mem_iff, Nat.card_eq_fintype_card]
  decide +kernel

private theorem section_count_row_9 : binaryVectorOfMask 4 9 ≠ 0 →
    Nat.card {i : Fin 128 // rowAction i (sectionMap (binaryVectorOfMask 4 9)) -
      sectionMap (binaryVectorOfMask 4 9) ∈ radical.space} ≤ 16 := by
  simp only [BinaryCoordinateSpace.mem_iff, Nat.card_eq_fintype_card]
  decide +kernel

private theorem section_count_row_10 : binaryVectorOfMask 4 10 ≠ 0 →
    Nat.card {i : Fin 128 // rowAction i (sectionMap (binaryVectorOfMask 4 10)) -
      sectionMap (binaryVectorOfMask 4 10) ∈ radical.space} ≤ 16 := by
  simp only [BinaryCoordinateSpace.mem_iff, Nat.card_eq_fintype_card]
  decide +kernel

private theorem section_count_row_11 : binaryVectorOfMask 4 11 ≠ 0 →
    Nat.card {i : Fin 128 // rowAction i (sectionMap (binaryVectorOfMask 4 11)) -
      sectionMap (binaryVectorOfMask 4 11) ∈ radical.space} ≤ 16 := by
  simp only [BinaryCoordinateSpace.mem_iff, Nat.card_eq_fintype_card]
  decide +kernel

private theorem section_count_row_12 : binaryVectorOfMask 4 12 ≠ 0 →
    Nat.card {i : Fin 128 // rowAction i (sectionMap (binaryVectorOfMask 4 12)) -
      sectionMap (binaryVectorOfMask 4 12) ∈ radical.space} ≤ 16 := by
  simp only [BinaryCoordinateSpace.mem_iff, Nat.card_eq_fintype_card]
  decide +kernel

private theorem section_count_row_13 : binaryVectorOfMask 4 13 ≠ 0 →
    Nat.card {i : Fin 128 // rowAction i (sectionMap (binaryVectorOfMask 4 13)) -
      sectionMap (binaryVectorOfMask 4 13) ∈ radical.space} ≤ 16 := by
  simp only [BinaryCoordinateSpace.mem_iff, Nat.card_eq_fintype_card]
  decide +kernel

private theorem section_count_row_14 : binaryVectorOfMask 4 14 ≠ 0 →
    Nat.card {i : Fin 128 // rowAction i (sectionMap (binaryVectorOfMask 4 14)) -
      sectionMap (binaryVectorOfMask 4 14) ∈ radical.space} ≤ 16 := by
  simp only [BinaryCoordinateSpace.mem_iff, Nat.card_eq_fintype_card]
  decide +kernel

private theorem section_count_row_15 : binaryVectorOfMask 4 15 ≠ 0 →
    Nat.card {i : Fin 128 // rowAction i (sectionMap (binaryVectorOfMask 4 15)) -
      sectionMap (binaryVectorOfMask 4 15) ∈ radical.space} ≤ 16 := by
  simp only [BinaryCoordinateSpace.mem_iff, Nat.card_eq_fintype_card]
  decide +kernel

private theorem section_count_rows (n : Fin 16) : binaryVectorOfMask 4 n.val ≠ 0 →
    Nat.card {i : Fin 128 // rowAction i (sectionMap (binaryVectorOfMask 4 n.val)) -
      sectionMap (binaryVectorOfMask 4 n.val) ∈ radical.space} ≤ 16 := by
  fin_cases n

  · exact section_count_row_0

  · exact section_count_row_1

  · exact section_count_row_2

  · exact section_count_row_3

  · exact section_count_row_4

  · exact section_count_row_5

  · exact section_count_row_6

  · exact section_count_row_7

  · exact section_count_row_8

  · exact section_count_row_9

  · exact section_count_row_10

  · exact section_count_row_11

  · exact section_count_row_12

  · exact section_count_row_13

  · exact section_count_row_14

  · exact section_count_row_15

theorem section_count : ∀ c : Fin 4 → ZMod 2, c ≠ 0 →
    Nat.card {i : Fin 128 // rowAction i (sectionMap c) - sectionMap c ∈ radical.space} ≤ 16 := by
  intro c hc
  obtain ⟨n, rfl⟩ := quotient_coordinates_surjective c
  exact section_count_rows n hc


end SymmetricSubgroupAsymptotics.BinarySplitRegular46FullConstantStabilizer
