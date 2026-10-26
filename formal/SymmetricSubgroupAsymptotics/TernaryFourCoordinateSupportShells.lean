import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Tactic.FinCases

/-! Five support shells of the literal four-coordinate ternary module.
The selected reductions contain only its 81 coordinate vectors; no
matrices, permutation groups, actions or subgroups are enumerated. -/
set_option autoImplicit false
set_option Elab.async false
namespace SymmetricSubgroupAsymptotics.TernaryFourCoordinateSupportShells

def supportSize (v : Fin 4 → ZMod 3) : ℕ :=
  (Finset.univ.filter fun i => v i≠0).card

def shell (k : ℕ) : Finset (Fin 4 → ZMod 3) :=
  Finset.univ.filter fun v => supportSize v=k

theorem supportSize_le_four (v : Fin 4 → ZMod 3) : supportSize v≤4 := by
  exact (Finset.card_filter_le _ _).trans_eq (by decide)

theorem shell_card (k : Fin 5) :
    (shell k.val).card=(if k.val=0 then 1 else if k.val=1 then 8
      else if k.val=2 then 24 else if k.val=3 then 32 else 16) := by
  fin_cases k <;> decide +kernel

end SymmetricSubgroupAsymptotics.TernaryFourCoordinateSupportShells
