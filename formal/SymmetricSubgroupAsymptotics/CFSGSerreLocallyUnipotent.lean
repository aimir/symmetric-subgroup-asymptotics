import Mathlib.Algebra.Module.LinearMap.End
import Mathlib.Algebra.Module.Submodule.Equiv
import Mathlib.Algebra.Ring.GeomSum

/-! A pointwise locally nilpotent perturbation of the identity is an
actual linear equivalence, with a finite geometric inverse at each point.
No global exponent or finite-dimensionality is assumed. -/
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators
namespace SymmetricSubgroupAsymptotics.CFSGSerreLocalNilpotence
variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

theorem one_sub_bijective_of_locally_nilpotent (D : Module.End R M)
    (hD : ∀ x : M, ∃ n : ℕ, (D ^ n) x = 0) : Function.Bijective (1 - D : Module.End R M) := by
  constructor
  · intro x y hxy
    have hker : (1 - D : Module.End R M) (x - y) = 0 := by
      rw [map_sub, hxy, sub_self]
    change (x - y) - D (x - y) = 0 at hker
    have hfix : D (x - y) = x - y := (sub_eq_zero.mp hker).symm
    have hpow : ∀ k : ℕ, (D ^ k) (x - y) = x - y := by
      intro k
      induction k with
      | zero => rfl
      | succ k ih => rw [pow_succ', Module.End.mul_apply, ih, hfix]
    obtain ⟨n, hn⟩ := hD (x - y)
    exact sub_eq_zero.mp ((hpow n).symm.trans hn)
  · intro x
    obtain ⟨n, hn⟩ := hD x
    refine ⟨(∑ k ∈ Finset.range n, D ^ k) x, ?_⟩
    have h := congrArg (fun f : Module.End R M => f x) (mul_neg_geom_sum D n)
    simpa only [Module.End.mul_apply, LinearMap.sub_apply, Module.End.one_apply, hn, sub_zero] using h

theorem one_add_bijective_of_locally_nilpotent (D : Module.End R M)
    (hD : ∀ x : M, ∃ n : ℕ, (D ^ n) x = 0) : Function.Bijective (1 + D : Module.End R M) := by
  have hneg : ∀ x : M, ∃ n : ℕ, ((-D) ^ n) x = 0 := by
    intro x
    obtain ⟨n, hn⟩ := hD x
    refine ⟨n, ?_⟩
    rw [neg_pow, Module.End.mul_apply, hn, map_zero]
  simpa only [sub_neg_eq_add] using one_sub_bijective_of_locally_nilpotent (-D) hneg

def locallyUnipotentEquiv (D : Module.End R M) (hD : ∀ x : M, ∃ n : ℕ, (D ^ n) x = 0) : M ≃ₗ[R] M :=
  LinearEquiv.ofBijective (1 + D) (one_add_bijective_of_locally_nilpotent D hD)

end SymmetricSubgroupAsymptotics.CFSGSerreLocalNilpotence
