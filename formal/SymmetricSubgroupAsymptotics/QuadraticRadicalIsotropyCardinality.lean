import Mathlib.LinearAlgebra.QuadraticForm.Radical
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.FieldTheory.Finiteness
import Lean.Elab.Tactic.Omega

/-! A totally singular subspace has at most half the ambient dimension
when the quadratic radical is zero.  The polar form itself may have a
nonzero radical, so this applies to odd-dimensional quadratic spaces in
characteristic two without pretending the polar pairing is nondegenerate. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.QuadraticRadicalIsotropyCardinality
open Module
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V]

omit [FiniteDimensional K V] in
theorem inf_polar_kernel_eq_bot (Q : QuadraticForm K V) (hQ : Q.radical = ⊥)
    (W : Submodule K V) (hW : ∀ v ∈ W, Q v = 0) : W ⊓ Q.polarBilin.ker = ⊥ := by
  apply eq_bot_iff.mpr
  intro v hv
  have hr : v ∈ Q.radical := ⟨hW v hv.1, hv.2⟩
  rwa [hQ] at hr

theorem twice_finrank_le (Q : QuadraticForm K V) (hQ : Q.radical = ⊥)
    (W : Submodule K V) (hW : ∀ v ∈ W, Q v = 0) :
    2 * Module.finrank K W ≤ Module.finrank K V := by
  have horth : W ≤ LinearMap.BilinForm.orthogonal Q.polarBilin W := by
    intro x hx
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro y hy
    change Q (y + x) - Q y - Q x = 0
    rw [hW _ (W.add_mem hy hx), hW y hy, hW x hx, sub_zero, sub_zero]
  have hdim := LinearMap.BilinForm.finrank_add_finrank_orthogonal' (B := Q.polarBilin) W
  rw [inf_polar_kernel_eq_bot Q hQ W hW, finrank_bot, add_zero] at hdim
  have hle := Submodule.finrank_mono horth
  omega

theorem finrank_le_of_odd_dimension (Q : QuadraticForm K V) (hQ : Q.radical = ⊥)
    (m : ℕ) (hdim : Module.finrank K V = 2 * m + 1)
    (W : Submodule K V) (hW : ∀ v ∈ W, Q v = 0) : Module.finrank K W ≤ m := by
  have h := twice_finrank_le Q hQ W hW
  omega

theorem card_le_of_odd_dimension [Finite K] (Q : QuadraticForm K V)
    (hQ : Q.radical = ⊥) (m : ℕ) (hdim : Module.finrank K V = 2 * m + 1)
    (W : Submodule K V) (hW : ∀ v ∈ W, Q v = 0) : Nat.card W ≤ Nat.card K ^ m := by
  rw [Module.natCard_eq_pow_finrank (K := K) (V := W)]
  exact Nat.pow_le_pow_right Nat.card_pos (finrank_le_of_odd_dimension Q hQ m hdim W hW)

end SymmetricSubgroupAsymptotics.QuadraticRadicalIsotropyCardinality
