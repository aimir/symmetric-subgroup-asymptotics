import Mathlib.GroupTheory.Subgroup.Center
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Group

/-! Finite filtration descent for actual central elements. Each step
removes a central factor in T and retains an actual next-tail remainder. -/
set_option autoImplicit false
set_option Elab.async false
namespace SymmetricSubgroupAsymptotics.CFSGFiniteFilteredCenter
variable {G : Type*} [Group G]

theorem center_le_of_filtered_steps (N : ℕ→Subgroup G) (T : Subgroup G) (H : ℕ)
    (hfirst : N 0=⊤) (hlast : N H=⊥)
    (hstep : ∀n,H>n→∀x∈N n,x∈Subgroup.center G→
      ∃t∈T,t∈Subgroup.center G ∧ ∃y∈N (n+1),x=t*y) :
    Subgroup.center G≤T := by
  have hall : ∀m n,m+n=H→∀x∈N n,x∈Subgroup.center G→x∈T := by
    intro m
    induction m with
    | zero =>
      intro n hn x hx hz
      have hnH : n=H := by omega
      rw [hnH,hlast,Subgroup.mem_bot] at hx
      rw [hx]
      exact T.one_mem
    | succ m ih =>
      intro n hn x hx hz
      obtain ⟨t,ht,htz,y,hy,he⟩ := hstep n (by omega) x hx hz
      have hyEq : y=t⁻¹*x := by rw [he];group
      have hyz : y∈Subgroup.center G := by
        rw [hyEq]
        exact (Subgroup.center G).mul_mem ((Subgroup.center G).inv_mem htz) hz
      have hyt := ih (n+1) (by omega) y hy hyz
      rw [he]
      exact T.mul_mem ht hyt
  intro x hx
  exact hall H 0 (by omega) x (by rw [hfirst];exact Subgroup.mem_top x) hx

end SymmetricSubgroupAsymptotics.CFSGFiniteFilteredCenter
