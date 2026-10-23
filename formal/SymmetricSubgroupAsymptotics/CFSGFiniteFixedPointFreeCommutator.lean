import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.Data.Finite.Card

/-! A fixed-point-free automorphism of a finite group has surjective
Lang map. When induced by ambient conjugation, the entire subgroup
therefore lies in the ambient derived subgroup. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGFiniteFixedPointFreeCommutator

variable {U : Type*} [Group U]

def langMap (tau : MulAut U) (u : U) : U := u⁻¹*tau u

theorem langMap_injective (tau : MulAut U)
    (hfixed : ∀ u, tau u=u → u=1) : Function.Injective (langMap tau) := by
  intro u v h
  have he : u⁻¹*tau u=v⁻¹*tau v := h
  have hx : tau (u*v⁻¹)=u*v⁻¹ := by
    rw [map_mul,map_inv]
    calc
      tau u*(tau v)⁻¹ = (u*(u⁻¹*tau u))*(tau v)⁻¹ := by simp
      _ = (u*(v⁻¹*tau v))*(tau v)⁻¹ := by rw [he]
      _ = u*v⁻¹ := by simp [mul_assoc]
  exact mul_inv_eq_one.mp (hfixed _ hx)

theorem langMap_surjective [Finite U] (tau : MulAut U)
    (hfixed : ∀ u, tau u=u → u=1) : Function.Surjective (langMap tau) :=
  Finite.surjective_of_injective (langMap_injective tau hfixed)

theorem subgroup_le_commutator {G : Type*} [Group G] (N : Subgroup G) [Finite N]
    (t : G) (tau : MulAut N)
    (hconj : ∀ u : N, (tau u : G)=t*(u : G)*t⁻¹)
    (hfixed : ∀ u, tau u=u → u=1) : N ≤ commutator G := by
  intro u hu
  obtain ⟨v,hv⟩ := langMap_surjective tau hfixed (⟨u,hu⟩ : N)
  have he := congrArg (fun z : N => (z : G)) hv
  change (v : G)⁻¹*(tau v : G)=u at he
  rw [hconj] at he
  rw [←he,commutator_eq_closure]
  simpa only [commutatorElement_def, inv_inv, mul_assoc] using
    Subgroup.subset_closure (commutator_mem_commutatorSet (v : G)⁻¹ t)

end SymmetricSubgroupAsymptotics.CFSGFiniteFixedPointFreeCommutator
