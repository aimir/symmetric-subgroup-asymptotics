import Mathlib.RepresentationTheory.Basic
import Mathlib.GroupTheory.OrderOfElement

/-! Point stabilizers modulo the actual smaller radical control an
original kernel. A bijective finite row action and checked scalar tests
give the order comparison; no maximal-subgroup catalogue is required. -/
set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics

/-- If every point outside U has too small a stabilizer modulo R, a
larger actual subgroup acting trivially on K modulo R forces K≤U. -/
theorem submodule_le_of_small_stabilizer_rows
    {k H V : Type*} [Field k] [Group H] [AddCommGroup V] [Module k V]
    {r : ℕ} (row : Fin r → H) (hrow : Function.Bijective row)
    (rho : Representation k H V) (U R K : Submodule k V) (cap : ℕ)
    (hcount : ∀ v, v ∉ U →
      Nat.card {i : Fin r // rho (row i) v - v ∈ R} ≤ cap)
    (D : Subgroup H) (hD : cap < Nat.card D)
    (hfixed : ∀ d : D, ∀ v ∈ K, rho (d : H) v - v ∈ R) :
    K ≤ U := by
  letI : Finite H := Finite.of_surjective row hrow.2
  let e : Fin r ≃ H := Equiv.ofBijective row hrow
  intro v hv
  by_contra hn
  let S := {i : Fin r // rho (row i) v - v ∈ R}
  let f : D → S := fun d => ⟨e.symm (d : H), by
    change rho (e (e.symm (d : H))) v - v ∈ R
    rw [e.apply_symm_apply]
    exact hfixed d v hv⟩
  have hf : Function.Injective f := by
    intro a b he
    apply Subtype.ext
    apply e.symm.injective
    exact congrArg Subtype.val he
  have hc : Nat.card D ≤ Nat.card S := Nat.card_le_card_of_injective f hf
  exact (not_lt_of_ge (hc.trans (hcount v hn))) hD

end SymmetricSubgroupAsymptotics
