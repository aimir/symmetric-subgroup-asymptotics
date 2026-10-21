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
namespace SymmetricSubgroupAsymptotics.BinarySplitElementary16PhiZeroStabilizer
local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
abbrev V := Fin 16 → ZMod 2
private def wBasis : Fin 11 → ℕ := ![34560,19200,11520,7680,129,65,33,17,9,5,3]
private def wDual : Fin 11 → ℕ := ![32768,16384,8192,4096,128,64,32,16,8,4,2]
private def rBasis : Fin 5 → ℕ := ![65280,135,75,45,30]
private def rDual : Fin 5 → ℕ := ![32768,128,64,32,16]
private def wInclusion := (binaryRectangularMatrixOfColumnMasks 16 11 wBasis).mulVecLin
private def wCoordinates := (binaryRectangularMatrixOfColumnMasks 11 16
  (fun i => binaryVectorMask (fun j => (binaryVectorOfMask 16 (wDual j)) i)) ).mulVecLin
private def rInclusion := (binaryRectangularMatrixOfColumnMasks 16 5 rBasis).mulVecLin
private def rCoordinates := (binaryRectangularMatrixOfColumnMasks 5 16
  (fun i => binaryVectorMask (fun j => (binaryVectorOfMask 16 (rDual j)) i)) ).mulVecLin
private theorem w_basis : ∀ i : Fin 11,
    wCoordinates (wInclusion (Pi.single i 1)) = Pi.single i 1 := by decide +kernel
private theorem r_basis : ∀ i : Fin 5,
    rCoordinates (rInclusion (Pi.single i 1)) = Pi.single i 1 := by decide +kernel
private theorem w_left_inverse (v : Fin 11 → ZMod 2) : wCoordinates (wInclusion v) = v := by
  have he : wCoordinates.comp wInclusion = LinearMap.id := by
    apply LinearMap.pi_ext
    intro i c
    have hs : Pi.single i c = c • Pi.single i (1 : ZMod 2) := by
      ext j
      simp [Pi.single_apply, mul_ite]
    simp only [LinearMap.comp_apply, hs, map_smul, w_basis, LinearMap.id_apply]
  exact DFunLike.congr_fun he v
private theorem r_left_inverse (v : Fin 5 → ZMod 2) : rCoordinates (rInclusion v) = v := by
  have he : rCoordinates.comp rInclusion = LinearMap.id := by
    apply LinearMap.pi_ext
    intro i c
    have hs : Pi.single i c = c • Pi.single i (1 : ZMod 2) := by
      ext j
      simp [Pi.single_apply, mul_ite]
    simp only [LinearMap.comp_apply, hs, map_smul, r_basis, LinearMap.id_apply]
  exact DFunLike.congr_fun he v

def state : BinaryCoordinateSpace 16 11 := ⟨wInclusion, wCoordinates, w_left_inverse⟩
def radical : BinaryCoordinateSpace 16 5 := ⟨rInclusion, rCoordinates, r_left_inverse⟩
def projection := (binaryRectangularMatrixOfColumnMasks 5 16
  (![1,1,1,1,1,1,1,1,2,4,8,16,28,26,22,14] : Fin 16 → ℕ)).mulVecLin
def sectionMap := (binaryRectangularMatrixOfColumnMasks 16 5
  (![1,256,512,1024,2048] : Fin 5 → ℕ)).mulVecLin
private def inverseImages : Fin 16 → Fin 8 → Fin 8 := ![![0,1,2,3,4,5,6,7],![0,1,2,3,4,5,6,7],![1,0,7,6,5,4,3,2],![1,0,7,6,5,4,3,2],![2,7,0,5,6,3,4,1],![2,7,0,5,6,3,4,1],![3,6,5,0,7,2,1,4],![3,6,5,0,7,2,1,4],![4,5,6,7,0,1,2,3],![4,5,6,7,0,1,2,3],![5,4,3,2,1,0,7,6],![5,4,3,2,1,0,7,6],![6,3,4,1,2,7,0,5],![6,3,4,1,2,7,0,5],![7,2,1,4,3,6,5,0],![7,2,1,4,3,6,5,0]]
private def forwardImages : Fin 16 → Fin 8 → Fin 8 := ![![0,1,2,3,4,5,6,7],![0,1,2,3,4,5,6,7],![1,0,7,6,5,4,3,2],![1,0,7,6,5,4,3,2],![2,7,0,5,6,3,4,1],![2,7,0,5,6,3,4,1],![3,6,5,0,7,2,1,4],![3,6,5,0,7,2,1,4],![4,5,6,7,0,1,2,3],![4,5,6,7,0,1,2,3],![5,4,3,2,1,0,7,6],![5,4,3,2,1,0,7,6],![6,3,4,1,2,7,0,5],![6,3,4,1,2,7,0,5],![7,2,1,4,3,6,5,0],![7,2,1,4,3,6,5,0]]
private def offsetMasks : Fin 16 → ℕ := ![0,255,0,255,0,255,0,255,0,255,0,255,0,255,0,255]
private theorem images_inverse : ∀ i j, inverseImages i (forwardImages i j) = j := by decide +kernel
private theorem images_forward : ∀ i j, forwardImages i (inverseImages i j) = j := by decide +kernel

def topPermutation (i : Fin 16) : Equiv.Perm (Fin 8) := {
  toFun := forwardImages i
  invFun := inverseImages i
  left_inv := images_inverse i
  right_inv := images_forward i }
def destinationOffset (i : Fin 16) : Fin 8 → ZMod 2 := binaryVectorOfMask 8 (offsetMasks i)
def rowAction (i : Fin 16) : V →ₗ[ZMod 2] V :=
  (BinaryPairFrame.pairLayerFlatten (w := 8)).toLinearMap.comp
    ((BinaryPairFrame.affinePairLayerMap (topPermutation i) (destinationOffset i)).comp
      (BinaryPairFrame.pairLayerFlatten (w := 8)).symm.toLinearMap)
theorem quotient_basis : ∀ j : Fin 16,
    Pi.single j 1 - sectionMap (projection (Pi.single j 1)) ∈ state.space := by
  simp only [BinaryCoordinateSpace.mem_iff]
  decide +kernel
private def killBasisRow (n : Fin 176) : Prop :=
  rowAction (finProdFinEquiv.symm n : Fin 16 × Fin 11).1
    (state.inclusion (Pi.single (finProdFinEquiv.symm n : Fin 16 × Fin 11).2 1)) -
    state.inclusion (Pi.single (finProdFinEquiv.symm n : Fin 16 × Fin 11).2 1) ∈ radical.space

private theorem kill_basis_block_0 : ∀ s : Fin 8,
    ∀ hs : 8 * 0 + s.val < 176, killBasisRow ⟨8 * 0 + s.val, hs⟩ := by
  simp only [killBasisRow, BinaryCoordinateSpace.mem_iff]
  decide +kernel

private theorem kill_basis_block_1 : ∀ s : Fin 8,
    ∀ hs : 8 * 1 + s.val < 176, killBasisRow ⟨8 * 1 + s.val, hs⟩ := by
  simp only [killBasisRow, BinaryCoordinateSpace.mem_iff]
  decide +kernel

private theorem kill_basis_block_2 : ∀ s : Fin 8,
    ∀ hs : 8 * 2 + s.val < 176, killBasisRow ⟨8 * 2 + s.val, hs⟩ := by
  simp only [killBasisRow, BinaryCoordinateSpace.mem_iff]
  decide +kernel

private theorem kill_basis_block_3 : ∀ s : Fin 8,
    ∀ hs : 8 * 3 + s.val < 176, killBasisRow ⟨8 * 3 + s.val, hs⟩ := by
  simp only [killBasisRow, BinaryCoordinateSpace.mem_iff]
  decide +kernel

private theorem kill_basis_block_4 : ∀ s : Fin 8,
    ∀ hs : 8 * 4 + s.val < 176, killBasisRow ⟨8 * 4 + s.val, hs⟩ := by
  simp only [killBasisRow, BinaryCoordinateSpace.mem_iff]
  decide +kernel

private theorem kill_basis_block_5 : ∀ s : Fin 8,
    ∀ hs : 8 * 5 + s.val < 176, killBasisRow ⟨8 * 5 + s.val, hs⟩ := by
  simp only [killBasisRow, BinaryCoordinateSpace.mem_iff]
  decide +kernel

private theorem kill_basis_block_6 : ∀ s : Fin 8,
    ∀ hs : 8 * 6 + s.val < 176, killBasisRow ⟨8 * 6 + s.val, hs⟩ := by
  simp only [killBasisRow, BinaryCoordinateSpace.mem_iff]
  decide +kernel

private theorem kill_basis_block_7 : ∀ s : Fin 8,
    ∀ hs : 8 * 7 + s.val < 176, killBasisRow ⟨8 * 7 + s.val, hs⟩ := by
  simp only [killBasisRow, BinaryCoordinateSpace.mem_iff]
  decide +kernel

private theorem kill_basis_block_8 : ∀ s : Fin 8,
    ∀ hs : 8 * 8 + s.val < 176, killBasisRow ⟨8 * 8 + s.val, hs⟩ := by
  simp only [killBasisRow, BinaryCoordinateSpace.mem_iff]
  decide +kernel

private theorem kill_basis_block_9 : ∀ s : Fin 8,
    ∀ hs : 8 * 9 + s.val < 176, killBasisRow ⟨8 * 9 + s.val, hs⟩ := by
  simp only [killBasisRow, BinaryCoordinateSpace.mem_iff]
  decide +kernel

private theorem kill_basis_block_10 : ∀ s : Fin 8,
    ∀ hs : 8 * 10 + s.val < 176, killBasisRow ⟨8 * 10 + s.val, hs⟩ := by
  simp only [killBasisRow, BinaryCoordinateSpace.mem_iff]
  decide +kernel

private theorem kill_basis_block_11 : ∀ s : Fin 8,
    ∀ hs : 8 * 11 + s.val < 176, killBasisRow ⟨8 * 11 + s.val, hs⟩ := by
  simp only [killBasisRow, BinaryCoordinateSpace.mem_iff]
  decide +kernel

private theorem kill_basis_block_12 : ∀ s : Fin 8,
    ∀ hs : 8 * 12 + s.val < 176, killBasisRow ⟨8 * 12 + s.val, hs⟩ := by
  simp only [killBasisRow, BinaryCoordinateSpace.mem_iff]
  decide +kernel

private theorem kill_basis_block_13 : ∀ s : Fin 8,
    ∀ hs : 8 * 13 + s.val < 176, killBasisRow ⟨8 * 13 + s.val, hs⟩ := by
  simp only [killBasisRow, BinaryCoordinateSpace.mem_iff]
  decide +kernel

private theorem kill_basis_block_14 : ∀ s : Fin 8,
    ∀ hs : 8 * 14 + s.val < 176, killBasisRow ⟨8 * 14 + s.val, hs⟩ := by
  simp only [killBasisRow, BinaryCoordinateSpace.mem_iff]
  decide +kernel

private theorem kill_basis_block_15 : ∀ s : Fin 8,
    ∀ hs : 8 * 15 + s.val < 176, killBasisRow ⟨8 * 15 + s.val, hs⟩ := by
  simp only [killBasisRow, BinaryCoordinateSpace.mem_iff]
  decide +kernel

private theorem kill_basis_block_16 : ∀ s : Fin 8,
    ∀ hs : 8 * 16 + s.val < 176, killBasisRow ⟨8 * 16 + s.val, hs⟩ := by
  simp only [killBasisRow, BinaryCoordinateSpace.mem_iff]
  decide +kernel

private theorem kill_basis_block_17 : ∀ s : Fin 8,
    ∀ hs : 8 * 17 + s.val < 176, killBasisRow ⟨8 * 17 + s.val, hs⟩ := by
  simp only [killBasisRow, BinaryCoordinateSpace.mem_iff]
  decide +kernel

private theorem kill_basis_block_18 : ∀ s : Fin 8,
    ∀ hs : 8 * 18 + s.val < 176, killBasisRow ⟨8 * 18 + s.val, hs⟩ := by
  simp only [killBasisRow, BinaryCoordinateSpace.mem_iff]
  decide +kernel

private theorem kill_basis_block_19 : ∀ s : Fin 8,
    ∀ hs : 8 * 19 + s.val < 176, killBasisRow ⟨8 * 19 + s.val, hs⟩ := by
  simp only [killBasisRow, BinaryCoordinateSpace.mem_iff]
  decide +kernel

private theorem kill_basis_block_20 : ∀ s : Fin 8,
    ∀ hs : 8 * 20 + s.val < 176, killBasisRow ⟨8 * 20 + s.val, hs⟩ := by
  simp only [killBasisRow, BinaryCoordinateSpace.mem_iff]
  decide +kernel

private theorem kill_basis_block_21 : ∀ s : Fin 8,
    ∀ hs : 8 * 21 + s.val < 176, killBasisRow ⟨8 * 21 + s.val, hs⟩ := by
  simp only [killBasisRow, BinaryCoordinateSpace.mem_iff]
  decide +kernel

private theorem kill_basis_rows (n : Fin 176) : killBasisRow n := by
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

theorem kill_basis (i : Fin 16) (j : Fin 11) :
    rowAction i (state.inclusion (Pi.single j 1)) - state.inclusion (Pi.single j 1) ∈ radical.space := by
  have h := kill_basis_rows (finProdFinEquiv (i, j))
  simpa only [killBasisRow, Equiv.symm_apply_apply] using h
private theorem quotient_coordinates_surjective :
    Function.Surjective (fun n : Fin 32 => binaryVectorOfMask 5 n.val) := by
  change ∀ c : Fin 5 → ZMod 2, ∃ n : Fin 32, binaryVectorOfMask 5 n.val = c
  decide +kernel

private theorem section_count_row_0 : binaryVectorOfMask 5 0 ≠ 0 →
    Nat.card {i : Fin 16 // rowAction i (sectionMap (binaryVectorOfMask 5 0)) -
      sectionMap (binaryVectorOfMask 5 0) ∈ radical.space} ≤ 2 := by
  simp only [BinaryCoordinateSpace.mem_iff, Nat.card_eq_fintype_card]
  decide +kernel

private theorem section_count_row_1 : binaryVectorOfMask 5 1 ≠ 0 →
    Nat.card {i : Fin 16 // rowAction i (sectionMap (binaryVectorOfMask 5 1)) -
      sectionMap (binaryVectorOfMask 5 1) ∈ radical.space} ≤ 2 := by
  simp only [BinaryCoordinateSpace.mem_iff, Nat.card_eq_fintype_card]
  decide +kernel

private theorem section_count_row_2 : binaryVectorOfMask 5 2 ≠ 0 →
    Nat.card {i : Fin 16 // rowAction i (sectionMap (binaryVectorOfMask 5 2)) -
      sectionMap (binaryVectorOfMask 5 2) ∈ radical.space} ≤ 2 := by
  simp only [BinaryCoordinateSpace.mem_iff, Nat.card_eq_fintype_card]
  decide +kernel

private theorem section_count_row_3 : binaryVectorOfMask 5 3 ≠ 0 →
    Nat.card {i : Fin 16 // rowAction i (sectionMap (binaryVectorOfMask 5 3)) -
      sectionMap (binaryVectorOfMask 5 3) ∈ radical.space} ≤ 2 := by
  simp only [BinaryCoordinateSpace.mem_iff, Nat.card_eq_fintype_card]
  decide +kernel

private theorem section_count_row_4 : binaryVectorOfMask 5 4 ≠ 0 →
    Nat.card {i : Fin 16 // rowAction i (sectionMap (binaryVectorOfMask 5 4)) -
      sectionMap (binaryVectorOfMask 5 4) ∈ radical.space} ≤ 2 := by
  simp only [BinaryCoordinateSpace.mem_iff, Nat.card_eq_fintype_card]
  decide +kernel

private theorem section_count_row_5 : binaryVectorOfMask 5 5 ≠ 0 →
    Nat.card {i : Fin 16 // rowAction i (sectionMap (binaryVectorOfMask 5 5)) -
      sectionMap (binaryVectorOfMask 5 5) ∈ radical.space} ≤ 2 := by
  simp only [BinaryCoordinateSpace.mem_iff, Nat.card_eq_fintype_card]
  decide +kernel

private theorem section_count_row_6 : binaryVectorOfMask 5 6 ≠ 0 →
    Nat.card {i : Fin 16 // rowAction i (sectionMap (binaryVectorOfMask 5 6)) -
      sectionMap (binaryVectorOfMask 5 6) ∈ radical.space} ≤ 2 := by
  simp only [BinaryCoordinateSpace.mem_iff, Nat.card_eq_fintype_card]
  decide +kernel

private theorem section_count_row_7 : binaryVectorOfMask 5 7 ≠ 0 →
    Nat.card {i : Fin 16 // rowAction i (sectionMap (binaryVectorOfMask 5 7)) -
      sectionMap (binaryVectorOfMask 5 7) ∈ radical.space} ≤ 2 := by
  simp only [BinaryCoordinateSpace.mem_iff, Nat.card_eq_fintype_card]
  decide +kernel

private theorem section_count_row_8 : binaryVectorOfMask 5 8 ≠ 0 →
    Nat.card {i : Fin 16 // rowAction i (sectionMap (binaryVectorOfMask 5 8)) -
      sectionMap (binaryVectorOfMask 5 8) ∈ radical.space} ≤ 2 := by
  simp only [BinaryCoordinateSpace.mem_iff, Nat.card_eq_fintype_card]
  decide +kernel

private theorem section_count_row_9 : binaryVectorOfMask 5 9 ≠ 0 →
    Nat.card {i : Fin 16 // rowAction i (sectionMap (binaryVectorOfMask 5 9)) -
      sectionMap (binaryVectorOfMask 5 9) ∈ radical.space} ≤ 2 := by
  simp only [BinaryCoordinateSpace.mem_iff, Nat.card_eq_fintype_card]
  decide +kernel

private theorem section_count_row_10 : binaryVectorOfMask 5 10 ≠ 0 →
    Nat.card {i : Fin 16 // rowAction i (sectionMap (binaryVectorOfMask 5 10)) -
      sectionMap (binaryVectorOfMask 5 10) ∈ radical.space} ≤ 2 := by
  simp only [BinaryCoordinateSpace.mem_iff, Nat.card_eq_fintype_card]
  decide +kernel

private theorem section_count_row_11 : binaryVectorOfMask 5 11 ≠ 0 →
    Nat.card {i : Fin 16 // rowAction i (sectionMap (binaryVectorOfMask 5 11)) -
      sectionMap (binaryVectorOfMask 5 11) ∈ radical.space} ≤ 2 := by
  simp only [BinaryCoordinateSpace.mem_iff, Nat.card_eq_fintype_card]
  decide +kernel

private theorem section_count_row_12 : binaryVectorOfMask 5 12 ≠ 0 →
    Nat.card {i : Fin 16 // rowAction i (sectionMap (binaryVectorOfMask 5 12)) -
      sectionMap (binaryVectorOfMask 5 12) ∈ radical.space} ≤ 2 := by
  simp only [BinaryCoordinateSpace.mem_iff, Nat.card_eq_fintype_card]
  decide +kernel

private theorem section_count_row_13 : binaryVectorOfMask 5 13 ≠ 0 →
    Nat.card {i : Fin 16 // rowAction i (sectionMap (binaryVectorOfMask 5 13)) -
      sectionMap (binaryVectorOfMask 5 13) ∈ radical.space} ≤ 2 := by
  simp only [BinaryCoordinateSpace.mem_iff, Nat.card_eq_fintype_card]
  decide +kernel

private theorem section_count_row_14 : binaryVectorOfMask 5 14 ≠ 0 →
    Nat.card {i : Fin 16 // rowAction i (sectionMap (binaryVectorOfMask 5 14)) -
      sectionMap (binaryVectorOfMask 5 14) ∈ radical.space} ≤ 2 := by
  simp only [BinaryCoordinateSpace.mem_iff, Nat.card_eq_fintype_card]
  decide +kernel

private theorem section_count_row_15 : binaryVectorOfMask 5 15 ≠ 0 →
    Nat.card {i : Fin 16 // rowAction i (sectionMap (binaryVectorOfMask 5 15)) -
      sectionMap (binaryVectorOfMask 5 15) ∈ radical.space} ≤ 2 := by
  simp only [BinaryCoordinateSpace.mem_iff, Nat.card_eq_fintype_card]
  decide +kernel

private theorem section_count_row_16 : binaryVectorOfMask 5 16 ≠ 0 →
    Nat.card {i : Fin 16 // rowAction i (sectionMap (binaryVectorOfMask 5 16)) -
      sectionMap (binaryVectorOfMask 5 16) ∈ radical.space} ≤ 2 := by
  simp only [BinaryCoordinateSpace.mem_iff, Nat.card_eq_fintype_card]
  decide +kernel

private theorem section_count_row_17 : binaryVectorOfMask 5 17 ≠ 0 →
    Nat.card {i : Fin 16 // rowAction i (sectionMap (binaryVectorOfMask 5 17)) -
      sectionMap (binaryVectorOfMask 5 17) ∈ radical.space} ≤ 2 := by
  simp only [BinaryCoordinateSpace.mem_iff, Nat.card_eq_fintype_card]
  decide +kernel

private theorem section_count_row_18 : binaryVectorOfMask 5 18 ≠ 0 →
    Nat.card {i : Fin 16 // rowAction i (sectionMap (binaryVectorOfMask 5 18)) -
      sectionMap (binaryVectorOfMask 5 18) ∈ radical.space} ≤ 2 := by
  simp only [BinaryCoordinateSpace.mem_iff, Nat.card_eq_fintype_card]
  decide +kernel

private theorem section_count_row_19 : binaryVectorOfMask 5 19 ≠ 0 →
    Nat.card {i : Fin 16 // rowAction i (sectionMap (binaryVectorOfMask 5 19)) -
      sectionMap (binaryVectorOfMask 5 19) ∈ radical.space} ≤ 2 := by
  simp only [BinaryCoordinateSpace.mem_iff, Nat.card_eq_fintype_card]
  decide +kernel

private theorem section_count_row_20 : binaryVectorOfMask 5 20 ≠ 0 →
    Nat.card {i : Fin 16 // rowAction i (sectionMap (binaryVectorOfMask 5 20)) -
      sectionMap (binaryVectorOfMask 5 20) ∈ radical.space} ≤ 2 := by
  simp only [BinaryCoordinateSpace.mem_iff, Nat.card_eq_fintype_card]
  decide +kernel

private theorem section_count_row_21 : binaryVectorOfMask 5 21 ≠ 0 →
    Nat.card {i : Fin 16 // rowAction i (sectionMap (binaryVectorOfMask 5 21)) -
      sectionMap (binaryVectorOfMask 5 21) ∈ radical.space} ≤ 2 := by
  simp only [BinaryCoordinateSpace.mem_iff, Nat.card_eq_fintype_card]
  decide +kernel

private theorem section_count_row_22 : binaryVectorOfMask 5 22 ≠ 0 →
    Nat.card {i : Fin 16 // rowAction i (sectionMap (binaryVectorOfMask 5 22)) -
      sectionMap (binaryVectorOfMask 5 22) ∈ radical.space} ≤ 2 := by
  simp only [BinaryCoordinateSpace.mem_iff, Nat.card_eq_fintype_card]
  decide +kernel

private theorem section_count_row_23 : binaryVectorOfMask 5 23 ≠ 0 →
    Nat.card {i : Fin 16 // rowAction i (sectionMap (binaryVectorOfMask 5 23)) -
      sectionMap (binaryVectorOfMask 5 23) ∈ radical.space} ≤ 2 := by
  simp only [BinaryCoordinateSpace.mem_iff, Nat.card_eq_fintype_card]
  decide +kernel

private theorem section_count_row_24 : binaryVectorOfMask 5 24 ≠ 0 →
    Nat.card {i : Fin 16 // rowAction i (sectionMap (binaryVectorOfMask 5 24)) -
      sectionMap (binaryVectorOfMask 5 24) ∈ radical.space} ≤ 2 := by
  simp only [BinaryCoordinateSpace.mem_iff, Nat.card_eq_fintype_card]
  decide +kernel

private theorem section_count_row_25 : binaryVectorOfMask 5 25 ≠ 0 →
    Nat.card {i : Fin 16 // rowAction i (sectionMap (binaryVectorOfMask 5 25)) -
      sectionMap (binaryVectorOfMask 5 25) ∈ radical.space} ≤ 2 := by
  simp only [BinaryCoordinateSpace.mem_iff, Nat.card_eq_fintype_card]
  decide +kernel

private theorem section_count_row_26 : binaryVectorOfMask 5 26 ≠ 0 →
    Nat.card {i : Fin 16 // rowAction i (sectionMap (binaryVectorOfMask 5 26)) -
      sectionMap (binaryVectorOfMask 5 26) ∈ radical.space} ≤ 2 := by
  simp only [BinaryCoordinateSpace.mem_iff, Nat.card_eq_fintype_card]
  decide +kernel

private theorem section_count_row_27 : binaryVectorOfMask 5 27 ≠ 0 →
    Nat.card {i : Fin 16 // rowAction i (sectionMap (binaryVectorOfMask 5 27)) -
      sectionMap (binaryVectorOfMask 5 27) ∈ radical.space} ≤ 2 := by
  simp only [BinaryCoordinateSpace.mem_iff, Nat.card_eq_fintype_card]
  decide +kernel

private theorem section_count_row_28 : binaryVectorOfMask 5 28 ≠ 0 →
    Nat.card {i : Fin 16 // rowAction i (sectionMap (binaryVectorOfMask 5 28)) -
      sectionMap (binaryVectorOfMask 5 28) ∈ radical.space} ≤ 2 := by
  simp only [BinaryCoordinateSpace.mem_iff, Nat.card_eq_fintype_card]
  decide +kernel

private theorem section_count_row_29 : binaryVectorOfMask 5 29 ≠ 0 →
    Nat.card {i : Fin 16 // rowAction i (sectionMap (binaryVectorOfMask 5 29)) -
      sectionMap (binaryVectorOfMask 5 29) ∈ radical.space} ≤ 2 := by
  simp only [BinaryCoordinateSpace.mem_iff, Nat.card_eq_fintype_card]
  decide +kernel

private theorem section_count_row_30 : binaryVectorOfMask 5 30 ≠ 0 →
    Nat.card {i : Fin 16 // rowAction i (sectionMap (binaryVectorOfMask 5 30)) -
      sectionMap (binaryVectorOfMask 5 30) ∈ radical.space} ≤ 2 := by
  simp only [BinaryCoordinateSpace.mem_iff, Nat.card_eq_fintype_card]
  decide +kernel

private theorem section_count_row_31 : binaryVectorOfMask 5 31 ≠ 0 →
    Nat.card {i : Fin 16 // rowAction i (sectionMap (binaryVectorOfMask 5 31)) -
      sectionMap (binaryVectorOfMask 5 31) ∈ radical.space} ≤ 2 := by
  simp only [BinaryCoordinateSpace.mem_iff, Nat.card_eq_fintype_card]
  decide +kernel

private theorem section_count_rows (n : Fin 32) : binaryVectorOfMask 5 n.val ≠ 0 →
    Nat.card {i : Fin 16 // rowAction i (sectionMap (binaryVectorOfMask 5 n.val)) -
      sectionMap (binaryVectorOfMask 5 n.val) ∈ radical.space} ≤ 2 := by
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

  · exact section_count_row_16

  · exact section_count_row_17

  · exact section_count_row_18

  · exact section_count_row_19

  · exact section_count_row_20

  · exact section_count_row_21

  · exact section_count_row_22

  · exact section_count_row_23

  · exact section_count_row_24

  · exact section_count_row_25

  · exact section_count_row_26

  · exact section_count_row_27

  · exact section_count_row_28

  · exact section_count_row_29

  · exact section_count_row_30

  · exact section_count_row_31

theorem section_count : ∀ c : Fin 5 → ZMod 2, c ≠ 0 →
    Nat.card {i : Fin 16 // rowAction i (sectionMap c) - sectionMap c ∈ radical.space} ≤ 2 := by
  intro c hc
  obtain ⟨n, rfl⟩ := quotient_coordinates_surjective c
  exact section_count_rows n hc


end SymmetricSubgroupAsymptotics.BinarySplitElementary16PhiZeroStabilizer
