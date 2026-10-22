import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fintype.Fin
import Mathlib.Algebra.Module.Pi
import Lean.Elab.Tactic.Omega

/-! An ordered pair of distinct coordinate basis vectors is determined
by their sum over the ORIGINAL integer lattice, before any base change. -/
set_option autoImplicit false
namespace SymmetricSubgroupAsymptotics.CFSGOrderedPairSingleDegrees
variable {r : ℕ}

def pairDegree (p : {p : Fin r×Fin r // p.1<p.2}) : Fin r→ℤ :=
  (Pi.single p.val.1 (1:ℤ) : Fin r→ℤ)+Pi.single p.val.2 (1:ℤ)

theorem pairDegree_injective : Function.Injective (pairDegree (r:=r)) := by
  intro p q he
  have hmem (i : Fin r) : (i=p.val.1 ∨ i=p.val.2)↔(i=q.val.1 ∨ i=q.val.2) := by
    have hi := congrFun he i
    change (Pi.single p.val.1 (1:ℤ) : Fin r→ℤ) i+
        (Pi.single p.val.2 (1:ℤ) : Fin r→ℤ) i=
      (Pi.single q.val.1 (1:ℤ) : Fin r→ℤ) i+
        (Pi.single q.val.2 (1:ℤ) : Fin r→ℤ) i at hi
    by_cases hp1 : i=p.val.1 <;> by_cases hp2 : i=p.val.2 <;>
      by_cases hq1 : i=q.val.1 <;> by_cases hq2 : i=q.val.2 <;>
      simp_all [Pi.single_apply,eq_comm]
  have hp := p.property
  have hq := q.property
  have hpmin := (hmem p.val.1).mp (Or.inl rfl)
  have hqmin := (hmem q.val.1).mpr (Or.inl rfl)
  have hfirst : p.val.1=q.val.1 := by
    rcases hpmin with h|h
    · exact h
    · rcases hqmin with h'|h'
      · exact h'.symm
      · omega
  have hsecond : p.val.2=q.val.2 := by
    rcases (hmem p.val.2).mp (Or.inr rfl) with h|h
    · omega
    · exact h
  exact Subtype.ext (Prod.ext hfirst hsecond)

end SymmetricSubgroupAsymptotics.CFSGOrderedPairSingleDegrees
