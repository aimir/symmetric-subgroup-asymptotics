import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.FieldTheory.Finiteness
import Lean.Elab.Tactic.Omega

/-! The actual two-variable commuting-motion map has a dual kernel
consisting of the SAME two invariant functionals. Rank/nullity gives
its exact kernel cardinality, without a form, fixed-space estimate,
or separate worst-case bound for either operator. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.LinearMotionDualKernelCardinality

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

def motionMap (g h : Module.End K V) : (V × V) →ₗ[K] V :=
  (LinearMap.id - h).comp (LinearMap.fst K V V) -
    (LinearMap.id - g).comp (LinearMap.snd K V V)

theorem motionMap_apply (g h : Module.End K V) (p : V × V) :
    motionMap g h p = (p.1 - h p.1) - (p.2 - g p.2) := rfl

def jointInvariantDual (g h : Module.End K V) : Submodule K (Module.Dual K V) :=
  LinearMap.ker (g.dualMap - LinearMap.id) ⊓
    LinearMap.ker (h.dualMap - LinearMap.id)

theorem ker_motion_dualMap (g h : Module.End K V) :
    LinearMap.ker (motionMap g h).dualMap = jointInvariantDual g h := by
  ext φ
  constructor
  · intro hφ
    change (motionMap g h).dualMap φ = 0 at hφ
    change g.dualMap φ - φ = 0 ∧ h.dualMap φ - φ = 0
    constructor
    · apply LinearMap.ext
      intro v
      change φ (g v) - φ v = 0
      have hv := LinearMap.congr_fun hφ (0, v)
      change φ ((0 - h 0) - (v - g v)) = 0 at hv
      simpa only [map_zero, sub_zero, zero_sub, map_neg, map_sub, neg_sub] using hv
    · apply LinearMap.ext
      intro v
      change φ (h v) - φ v = 0
      have hv := LinearMap.congr_fun hφ (v, 0)
      change φ ((v - h v) - (0 - g 0)) = 0 at hv
      have hv' : φ v - φ (h v) = 0 := by
        simpa only [map_zero, sub_zero, map_sub] using hv
      exact sub_eq_zero.mpr (sub_eq_zero.mp hv').symm
  · intro hφ
    change g.dualMap φ - φ = 0 ∧ h.dualMap φ - φ = 0 at hφ
    rcases hφ with ⟨hg, hh⟩
    change (motionMap g h).dualMap φ = 0
    apply LinearMap.ext
    intro p
    change φ (motionMap g h p) = 0
    have hg' : φ (g p.2) = φ p.2 := by
      have he := LinearMap.congr_fun hg p.2
      change φ (g p.2) - φ p.2 = 0 at he
      exact sub_eq_zero.mp he
    have hh' : φ (h p.1) = φ p.1 := by
      have he := LinearMap.congr_fun hh p.1
      change φ (h p.1) - φ p.1 = 0 at he
      exact sub_eq_zero.mp he
    simp only [motionMap_apply, map_sub, hg', hh', sub_self]

theorem kernel_card_eq_card_mul_dual_kernel [Finite K] [Module.Finite K V]
    (f : (V × V) →ₗ[K] V) :
    Nat.card (LinearMap.ker f) = Nat.card V * Nat.card (LinearMap.ker f.dualMap) := by
  have hf := LinearMap.finrank_range_add_finrank_ker f
  have hd := LinearMap.finrank_range_add_finrank_ker f.dualMap
  rw [LinearMap.finrank_range_dualMap_eq_finrank_range, Subspace.dual_finrank_eq] at hd
  rw [Module.finrank_prod] at hf
  have he : Module.finrank K (LinearMap.ker f) =
      Module.finrank K V + Module.finrank K (LinearMap.ker f.dualMap) := by omega
  rw [Module.natCard_eq_pow_finrank (K := K) (V := LinearMap.ker f),
    Module.natCard_eq_pow_finrank (K := K) (V := V),
    Module.natCard_eq_pow_finrank (K := K) (V := LinearMap.ker f.dualMap), he, pow_add]

theorem motion_kernel_card [Finite K] [Module.Finite K V] (g h : Module.End K V) :
    Nat.card (LinearMap.ker (motionMap g h)) =
      Nat.card V * Nat.card (jointInvariantDual g h) := by
  rw [kernel_card_eq_card_mul_dual_kernel, ker_motion_dualMap]

end SymmetricSubgroupAsymptotics.LinearMotionDualKernelCardinality
