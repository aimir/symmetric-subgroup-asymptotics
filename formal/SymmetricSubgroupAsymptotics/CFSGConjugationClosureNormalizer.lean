import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Tactic.Group

/-! Conjugation-closure and a finite-order normalizer criterion.
No finiteness of the ambient group or of its subgroup is required. -/
set_option autoImplicit false
set_option Elab.async false
namespace SymmetricSubgroupAsymptotics.CFSGConjugationClosureNormalizer
variable {G : Type*} [Group G]

theorem conjugate_closure_mem (S : Set G) (g : G)
    (h : ∀x∈S,g*x*g⁻¹∈Subgroup.closure S) :
    ∀x∈Subgroup.closure S,g*x*g⁻¹∈Subgroup.closure S := by
  have hh : Subgroup.closure S≤(Subgroup.closure S).comap (MulAut.conj g).toMonoidHom := by
    apply (Subgroup.closure_le _).mpr
    intro x hx
    exact h x hx
  intro x hx
  exact hh hx

theorem mem_normalizer_of_conjugate_closed_of_pow_one (H : Subgroup G) (g : G)
    (h : ∀x∈H,g*x*g⁻¹∈H) (n : ℕ) (hn : 0<n) (hpow : g^n=1) :
    g∈Subgroup.normalizer (H : Set G) := by
  have hp : ∀k : ℕ,∀x∈H,g^k*x*(g^k)⁻¹∈H := by
    intro k
    induction k with
    | zero => intro x hx; simpa only [pow_zero,inv_one,one_mul,mul_one] using hx
    | succ k ih =>
      intro x hx
      have hh := ih (g*x*g⁻¹) (h x hx)
      simpa only [pow_succ,_root_.mul_inv_rev,mul_assoc] using hh
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · exact h x
  · intro hx
    have hh := hp (n-1) (g*x*g⁻¹) hx
    have hstep : g^(n-1)*g=1 := by
      rw [←pow_succ,Nat.sub_add_cancel (show 1≤n from hn),hpow]
    have he : g^(n-1)*(g*x*g⁻¹)*(g^(n-1))⁻¹=x := by
      calc
        _=(g^(n-1)*g)*x*(g^(n-1)*g)⁻¹ := by group
        _=x := by rw [hstep]; simp only [inv_one,one_mul,mul_one]
    exact he ▸ hh

end SymmetricSubgroupAsymptotics.CFSGConjugationClosureNormalizer
