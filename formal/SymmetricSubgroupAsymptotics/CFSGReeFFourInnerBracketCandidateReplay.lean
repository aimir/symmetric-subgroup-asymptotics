import SymmetricSubgroupAsymptotics.CFSGNormTwoCharTwoRootWordRewrite
import SymmetricSubgroupAsymptotics.CFSGReeFFourInnerBracketSquareSupports

/-! The ENTIRE EXACT 125-step recorded candidate trace.
Root and rule arithmetic are deduplicated; no exceptional fixedness is assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical Matrix
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourInnerBracketCandidateReplay
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing
open CFSGExceptionalCartanPositiveDefinite CFSGExceptionalNormTwoBases
open TwoLetterWordRewrite
local notation "A" => CartanMatrix.E₆
local notation "hd" => CartanMatrix.E₆_diag
local notation "hs" => CartanMatrix.E₆_transpose
local notation "hp" => E6_positive_definite
local notation "ho" => CartanMatrix.E₆_off_diag_nonpos

def vectors : Fin 21 → Fin 6 → ℤ :=
  ![![0,0,0,1,1,1],![0,0,1,1,1,1],![0,1,0,1,1,0],![0,1,1,1,0,0],![0,1,1,1,1,0],![0,1,1,1,1,1],![0,1,1,2,1,0],![0,1,1,2,1,1],![0,1,1,2,2,1],![1,0,1,1,0,0],![1,0,1,1,1,0],![1,0,1,1,1,1],![1,1,1,1,1,0],![1,1,1,2,1,0],![1,1,1,2,1,1],![1,1,1,2,2,1],![1,1,2,2,1,0],![1,1,2,2,1,1],![1,1,2,2,2,1],![1,1,2,3,2,1],![1,2,2,3,2,1]]

theorem root_properties : ∀ i : Fin 21, integerPairing A (vectors i) (vectors i)=2 ∧
    ∀ t : Fin 6, 0≤vectors i t := by decide +kernel

def root (i : Fin 21) : Roots A := ⟨vectors i,(root_properties i).1⟩

def initial : List (Fin 21) := [20,11,2,3,19,4,0,9,7,13,18,5,12,14,10,1,6]

def rules : Fin 115 → Rule (Fin 21) := ![.swap 2 3,.swap 2 19,.swap 3 19,.swap 11 19,.swap 2 4,.swap 3 4,.swap 0 9,.raise 2 9 13,.swap 3 13,.swap 4 13,.swap 11 13,.swap 3 9,.swap 0 7,.swap 2 7,.swap 3 7,.swap 9 7,.swap 4 7,.swap 11 7,.swap 0 13,.swap 2 13,.swap 9 13,.swap 7 13,.cancel 13,.swap 0 18,.swap 2 18,.swap 3 18,.swap 9 18,.swap 4 18,.swap 11 18,.swap 7 18,.swap 0 5,.swap 2 5,.swap 3 5,.raise 9 5 17,.swap 4 17,.swap 11 17,.swap 7 17,.swap 4 5,.raise 0 12 15,.swap 2 15,.raise 3 15 20,.swap 9 20,.swap 4 20,.swap 5 20,.swap 11 20,.swap 7 20,.swap 17 20,.swap 18 20,.swap 19 20,.cancel 20,.swap 9 15,.swap 4 15,.swap 5 15,.swap 11 15,.swap 7 15,.swap 2 12,.swap 3 12,.swap 9 12,.swap 4 12,.swap 5 12,.swap 11 12,.swap 0 14,.swap 2 14,.swap 3 14,.swap 9 14,.raise 4 14 20,.swap 12 20,.swap 15 20,.swap 5 14,.swap 11 14,.swap 12 14,.swap 7 14,.swap 0 10,.swap 2 10,.raise 3 10 16,.swap 9 16,.swap 4 16,.swap 5 16,.swap 11 16,.swap 12 16,.swap 7 16,.swap 14 16,.swap 9 10,.swap 4 10,.swap 0 1,.raise 2 1 8,.swap 3 8,.raise 9 8 19,.swap 4 19,.swap 10 19,.swap 5 19,.swap 12 19,.swap 7 19,.swap 14 19,.swap 16 19,.swap 15 19,.swap 17 19,.swap 18 19,.cancel 19,.swap 4 8,.swap 10 8,.swap 5 8,.swap 11 8,.swap 12 8,.swap 7 8,.swap 3 1,.swap 9 1,.swap 0 6,.swap 2 6,.swap 3 6,.swap 9 6,.swap 1 6,.swap 4 6,.swap 10 6,.swap 5 6]

def steps : List (Step (Fin 21)) := [
  ⟨2, rules 0⟩,
  ⟨3, rules 1⟩,
  ⟨2, rules 2⟩,
  ⟨1, rules 3⟩,
  ⟨4, rules 4⟩,
  ⟨3, rules 5⟩,
  ⟨6, rules 6⟩,
  ⟨5, rules 7⟩,
  ⟨4, rules 8⟩,
  ⟨3, rules 9⟩,
  ⟨2, rules 10⟩,
  ⟨5, rules 11⟩,
  ⟨8, rules 12⟩,
  ⟨7, rules 13⟩,
  ⟨6, rules 14⟩,
  ⟨5, rules 15⟩,
  ⟨4, rules 16⟩,
  ⟨3, rules 17⟩,
  ⟨9, rules 18⟩,
  ⟨8, rules 19⟩,
  ⟨7, rules 8⟩,
  ⟨6, rules 20⟩,
  ⟨5, rules 9⟩,
  ⟨4, rules 10⟩,
  ⟨3, rules 21⟩,
  ⟨2, rules 22⟩,
  ⟨8, rules 23⟩,
  ⟨7, rules 24⟩,
  ⟨6, rules 25⟩,
  ⟨5, rules 26⟩,
  ⟨4, rules 27⟩,
  ⟨3, rules 28⟩,
  ⟨2, rules 29⟩,
  ⟨9, rules 30⟩,
  ⟨8, rules 31⟩,
  ⟨7, rules 32⟩,
  ⟨6, rules 33⟩,
  ⟨5, rules 34⟩,
  ⟨4, rules 35⟩,
  ⟨3, rules 36⟩,
  ⟨6, rules 37⟩,
  ⟨11, rules 38⟩,
  ⟨10, rules 39⟩,
  ⟨9, rules 40⟩,
  ⟨8, rules 41⟩,
  ⟨7, rules 42⟩,
  ⟨6, rules 43⟩,
  ⟨5, rules 44⟩,
  ⟨4, rules 45⟩,
  ⟨3, rules 46⟩,
  ⟨2, rules 47⟩,
  ⟨1, rules 48⟩,
  ⟨0, rules 49⟩,
  ⟨7, rules 50⟩,
  ⟨6, rules 51⟩,
  ⟨5, rules 52⟩,
  ⟨4, rules 53⟩,
  ⟨3, rules 54⟩,
  ⟨10, rules 55⟩,
  ⟨9, rules 56⟩,
  ⟨8, rules 57⟩,
  ⟨7, rules 58⟩,
  ⟨6, rules 59⟩,
  ⟨5, rules 60⟩,
  ⟨12, rules 61⟩,
  ⟨11, rules 62⟩,
  ⟨10, rules 63⟩,
  ⟨9, rules 64⟩,
  ⟨8, rules 65⟩,
  ⟨7, rules 43⟩,
  ⟨6, rules 44⟩,
  ⟨5, rules 66⟩,
  ⟨4, rules 45⟩,
  ⟨3, rules 67⟩,
  ⟨2, rules 46⟩,
  ⟨1, rules 47⟩,
  ⟨0, rules 48⟩,
  ⟨8, rules 68⟩,
  ⟨7, rules 69⟩,
  ⟨6, rules 70⟩,
  ⟨5, rules 71⟩,
  ⟨14, rules 72⟩,
  ⟨13, rules 73⟩,
  ⟨12, rules 74⟩,
  ⟨11, rules 75⟩,
  ⟨10, rules 76⟩,
  ⟨9, rules 77⟩,
  ⟨8, rules 78⟩,
  ⟨7, rules 79⟩,
  ⟨6, rules 80⟩,
  ⟨5, rules 81⟩,
  ⟨12, rules 82⟩,
  ⟨11, rules 83⟩,
  ⟨16, rules 84⟩,
  ⟨15, rules 85⟩,
  ⟨14, rules 86⟩,
  ⟨13, rules 87⟩,
  ⟨12, rules 88⟩,
  ⟨11, rules 89⟩,
  ⟨10, rules 90⟩,
  ⟨9, rules 3⟩,
  ⟨8, rules 91⟩,
  ⟨7, rules 92⟩,
  ⟨6, rules 93⟩,
  ⟨5, rules 94⟩,
  ⟨4, rules 95⟩,
  ⟨3, rules 96⟩,
  ⟨2, rules 97⟩,
  ⟨1, rules 98⟩,
  ⟨11, rules 99⟩,
  ⟨10, rules 100⟩,
  ⟨9, rules 101⟩,
  ⟨8, rules 102⟩,
  ⟨7, rules 103⟩,
  ⟨6, rules 104⟩,
  ⟨14, rules 105⟩,
  ⟨13, rules 106⟩,
  ⟨17, rules 107⟩,
  ⟨16, rules 108⟩,
  ⟨15, rules 109⟩,
  ⟨14, rules 110⟩,
  ⟨13, rules 111⟩,
  ⟨12, rules 112⟩,
  ⟨11, rules 113⟩,
  ⟨10, rules 114⟩]

def result : List (Fin 21) := [20,18,17,15,16,14,8,7,12,11,6,5,10,4,1,9,3,2,0]

theorem rule_certificate : ∀ j : Fin 115,
    CFSGNormTwoCharTwoRootWordRewrite.validRule A root (rules j) := by decide +kernel

theorem step_rule_index : ∀ i : Fin steps.length,
    ∃ j : Fin 115, (steps.get i).rule = rules j := by decide +kernel

theorem rules_valid : ∀ s ∈ steps,
    CFSGNormTwoCharTwoRootWordRewrite.validRule A root s.rule := by
  have h : ∀ i : Fin steps.length,
      CFSGNormTwoCharTwoRootWordRewrite.validRule A root (steps.get i).rule := by
    intro i
    obtain ⟨j,hj⟩ := step_rule_index i
    rw [hj]
    exact rule_certificate j
  exact (List.forall_mem_iff_get (l := steps)
    (p := fun s => CFSGNormTwoCharTwoRootWordRewrite.validRule A root s.rule)).2 h

theorem run_eq : TwoLetterWordRewrite.run steps initial = some result := by decide +kernel

theorem collected (K : Type) [CommRing K] [CharP K 2] :
    value (CFSGNormTwoCharTwoRootWordRewrite.parameter A hd hs hp ho root K) initial =
      value (CFSGNormTwoCharTwoRootWordRewrite.parameter A hd hs hp ho root K) result :=
  CFSGNormTwoCharTwoRootWordRewrite.run_sound A hd hs hp ho root K
    (fun i t => (root_properties i).2 t) steps initial result rules_valid run_eq

end SymmetricSubgroupAsymptotics.CFSGReeFFourInnerBracketCandidateReplay
