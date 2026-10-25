import SymmetricSubgroupAsymptotics.CFSGNormTwoCharTwoRootWordRewrite
import SymmetricSubgroupAsymptotics.CFSGReeFFourInnerBracketSquareSupports

/-! Eight initial rewrites of the ONE designated candidate trace.
This is a selected semantic pilot, not the full candidate identity. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical Matrix
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourInnerBracketReplayPilot
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing
open CFSGExceptionalCartanPositiveDefinite CFSGExceptionalNormTwoBases
open TwoLetterWordRewrite
local notation "A" => CartanMatrix.E₆
local notation "hd" => CartanMatrix.E₆_diag
local notation "hs" => CartanMatrix.E₆_transpose
local notation "hp" => E6_positive_definite
local notation "ho" => CartanMatrix.E₆_off_diag_nonpos

def vectors : Fin 17 → Fin 6 → ℤ :=
  ![![0,0,0,1,1,1],![0,0,1,1,1,1],![0,1,0,1,1,0],![0,1,1,1,0,0],![0,1,1,1,1,0],![0,1,1,1,1,1],![0,1,1,2,1,0],![0,1,1,2,1,1],![1,0,1,1,0,0],![1,0,1,1,1,0],![1,0,1,1,1,1],![1,1,1,1,1,0],![1,1,1,2,1,0],![1,1,1,2,1,1],![1,1,2,2,2,1],![1,1,2,3,2,1],![1,2,2,3,2,1]]

theorem root_properties : ∀ i : Fin 17, integerPairing A (vectors i) (vectors i)=2 ∧
    ∀ t : Fin 6, 0≤vectors i t := by decide +kernel

def root (i : Fin 17) : Roots A := ⟨vectors i,(root_properties i).1⟩

def initial : List (Fin 17) := [16,10,2,3,15,4,0,8,7,12,14,5,11,13,9,1,6]

def steps : List (Step (Fin 17)) := [
  ⟨2, .swap 2 3⟩,
  ⟨3, .swap 2 15⟩,
  ⟨2, .swap 3 15⟩,
  ⟨1, .swap 10 15⟩,
  ⟨4, .swap 2 4⟩,
  ⟨3, .swap 3 4⟩,
  ⟨6, .swap 0 8⟩,
  ⟨5, .raise 2 8 12⟩]

def result : List (Fin 17) := [16,15,10,4,3,12,8,2,0,7,12,14,5,11,13,9,1,6]

theorem rules_valid : ∀ s ∈ steps,
    CFSGNormTwoCharTwoRootWordRewrite.validRule A root s.rule := by
  have h : ∀ i : Fin steps.length,
      CFSGNormTwoCharTwoRootWordRewrite.validRule A root (steps.get i).rule := by
    decide +kernel
  exact (List.forall_mem_iff_get (l := steps)
    (p := fun s => CFSGNormTwoCharTwoRootWordRewrite.validRule A root s.rule)).2 h

theorem run_eq : TwoLetterWordRewrite.run steps initial = some result := by decide +kernel

theorem collected (K : Type) [CommRing K] [CharP K 2] :
    value (CFSGNormTwoCharTwoRootWordRewrite.parameter A hd hs hp ho root K) initial =
      value (CFSGNormTwoCharTwoRootWordRewrite.parameter A hd hs hp ho root K) result :=
  CFSGNormTwoCharTwoRootWordRewrite.run_sound A hd hs hp ho root K
    (fun i t => (root_properties i).2 t) steps initial result rules_valid run_eq

end SymmetricSubgroupAsymptotics.CFSGReeFFourInnerBracketReplayPilot
