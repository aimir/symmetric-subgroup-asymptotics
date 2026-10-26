import SymmetricSubgroupAsymptotics.CFSGReeFFourShortPairedWeylMenu
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateBlockDiagramAction

/-! The sixteen retained short words have distinct actual root-block
permutations. Block equality is tested on the six original simple roots
and transported to the literal integral lattice matrices. The only finite
certificate is injectivity of these sixteen 6-by-6 matrices. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourShortWordBlockSeparation
open CFSGReeFFourShortPairedWeylMenu CFSGReeFFourFixedWordClassification
open CFSGTwistedE6FixedWordClassification CFSGNormTwoCoordinateLatticeWord
open CFSGSignedCartanReflections CFSGExceptionalCartanPositiveDefinite
open CFSGNormTwoCoordinateWeylBlocks CFSGNormTwoCoordinateBlockDiagramAction
open CFSGNormTwoRootPairing CFSGNormTwoGeckWeylLatticeLinear
open CFSGNormTwoGeckWeylWordDegree CFSGIntegerMatrixPairing
local notation "A" => CartanMatrix.E₆
local notation "hd" => CartanMatrix.E₆_diag
local notation "hs" => CartanMatrix.E₆_transpose
local notation "hp" => E6_positive_definite
local notation "ho" => CartanMatrix.E₆_off_diag_nonpos
local notation "b₀" => coordinateBase A hd hs hp ho
local notation "s₀" => coordinateIndexEquiv A hd hs hp ho

private theorem lattice_eq_of_block_eq (v w : List (Fin 6))
    (he : wordBlockPermutation A hd hs hp ho v=wordBlockPermutation A hd hs hp ho w) :
    latticeWord A v=latticeWord A w := by
  classical
  apply Matrix.ext_of_mulVec_single
  intro j
  have hr := block_equality_root_action A hd hs hp ho v w he (coordinateRoot A hd j)
  have hv := congrArg (fun k : Roots A => k.val) hr
  change (wordRoot A hs hp b₀ s₀ v (coordinateRoot A hd j)).val =
    (wordRoot A hs hp b₀ s₀ w (coordinateRoot A hd j)).val at hv
  rw [←wordLinear_root,←wordLinear_root] at hv
  change wordLinear A hs hp b₀ s₀ v (Pi.single j (1:ℤ)) =
    wordLinear A hs hp b₀ s₀ w (Pi.single j (1:ℤ)) at hv
  have hl := LinearMap.congr_fun (latticeWord_linear A hd hs hp ho v) (Pi.single j (1:ℤ))
  have hright := LinearMap.congr_fun (latticeWord_linear A hd hs hp ho w) (Pi.single j (1:ℤ))
  change latticeWord A v*ᵥ(Pi.single j (1:ℤ))=wordLinear A hs hp b₀ s₀ v (Pi.single j (1:ℤ)) at hl
  change latticeWord A w*ᵥ(Pi.single j (1:ℤ))=wordLinear A hs hp b₀ s₀ w (Pi.single j (1:ℤ)) at hright
  exact hl.trans (hv.trans hright.symm)

private theorem short_lattice_injective : Function.Injective (fun i : Fin 16 =>
    latticeWord A (expandRelative (expandPaired (shortWord i)))) := by
  decide +kernel

theorem short_block_action_injective : Function.Injective (fun i : Fin 16 =>
    wordBlockPermutation A hd hs hp ho (expandRelative (expandPaired (shortWord i)))) := by
  intro i j he
  exact short_lattice_injective (lattice_eq_of_block_eq _ _ he)

end SymmetricSubgroupAsymptotics.CFSGReeFFourShortWordBlockSeparation
