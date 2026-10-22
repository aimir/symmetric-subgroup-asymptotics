import SymmetricSubgroupAsymptotics.CFSGPermutationCrossSwapWords
import Mathlib.Tactic.FinCases
import Mathlib.Data.Fintype.Fin

/-! The two different double matchings on four original points commute.
These symbolic Klein-four identities supply the small alternating Sylow seed. -/
set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.CFSGPermutationKleinMatching
open CFSGPermutationCrossSwapWords

variable {X : Type*} [DecidableEq X]

theorem matching_commute (f : Fin 4 → X) (hf : Function.Injective f) :
    Commute (doubleSwap (f 0) (f 1) (f 2) (f 3))
      (doubleSwap (f 0) (f 2) (f 1) (f 3)) := by
  change _ * _ = _ * _
  ext x
  by_cases hx : x ∈ Set.range f
  · obtain ⟨i, rfl⟩ := hx
    fin_cases i <;>
      simp [doubleSwap, Equiv.Perm.mul_apply, Equiv.swap_apply_def, hf.eq_iff]
  · have hn : ∀ i : Fin 4, x ≠ f i := fun i h => hx ⟨i, h.symm⟩
    simp [doubleSwap, Equiv.Perm.mul_apply, Equiv.swap_apply_def, hn]

theorem paired_doubleSwap_commute (p : Equiv.Perm X) (u v a b : X)
    (hu : p u = v) (hv : p v = u) (ha : p a = a) (hb : p b = b) :
    Commute (doubleSwap u v a b) p := by
  have hc : p * doubleSwap u v a b * p⁻¹ = doubleSwap u v a b := by
    change (MulAut.conj p) (Equiv.swap u v * Equiv.swap a b) = _
    rw [map_mul]
    change (p * Equiv.swap u v * p⁻¹) * (p * Equiv.swap a b * p⁻¹) = _
    rw [← Equiv.swap_apply_apply, ← Equiv.swap_apply_apply, hu, hv, ha, hb, Equiv.swap_comm v u]
    rfl
  exact ((mul_inv_eq_iff_eq_mul).mp hc).symm

end SymmetricSubgroupAsymptotics.CFSGPermutationKleinMatching
