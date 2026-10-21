import Mathlib.Data.Fin.Basic
import Lean.Elab.Tactic.Omega

/-! Reassemble separately checked blocks of at most eight finite rows.
The dispatcher has no access to the contents of any row. -/
set_option autoImplicit false
namespace SymmetricSubgroupAsymptotics.FiniteEightRowSlices

theorem apply {n : ℕ} (P : Fin n → Prop)
    (h : ∀ q : Fin ((n + 7) / 8), ∀ r : Fin 8,
      ∀ hr : 8 * q.val + r.val < n, P ⟨8 * q.val + r.val, hr⟩)
    (i : Fin n) : P i := by
  let q : Fin ((n + 7) / 8) := ⟨i.val / 8, by omega⟩
  let r : Fin 8 := ⟨i.val % 8, Nat.mod_lt _ (by decide)⟩
  have hr : 8 * q.val + r.val < n := by
    dsimp only [q, r]
    omega
  have he : (⟨8 * q.val + r.val, hr⟩ : Fin n) = i := by
    apply Fin.ext
    dsimp only [q, r]
    omega
  simpa only [he] using h q r hr

end SymmetricSubgroupAsymptotics.FiniteEightRowSlices
