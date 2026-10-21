import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.GroupTheory.Subgroup.Centralizer
import Mathlib.GroupTheory.QuotientGroup.Basic

/-! Mixed commutators of literal generated subgroups can be checked on
their original generators, retaining an arbitrary normal container. -/
set_option autoImplicit false
noncomputable section
open scoped commutatorElement
namespace SymmetricSubgroupAsymptotics

theorem mixedCommutator_le_of_generator_checks
    {G I J : Type*} [Group G] (f : I → G) (g : J → G)
    (C : Subgroup G) [C.Normal]
    (hcheck : ∀ i j, ⁅f i,g j⁆∈C) :
    ⁅Subgroup.closure (Set.range f),Subgroup.closure (Set.range g)⁆≤C := by
  let q := QuotientGroup.mk' C
  have hlocal (i : I) : Subgroup.closure (Set.range g)≤
      (Subgroup.centralizer ({q (f i)} : Set (G ⧸ C))).comap q := by
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨j,rfl⟩
    apply Subgroup.mem_centralizer_singleton_iff.mpr
    have h := (QuotientGroup.eq_one_iff ⁅f i,g j⁆).mpr (hcheck i j)
    change q ⁅f i,g j⁆=1 at h
    rw [map_commutatorElement,commutatorElement_eq_one_iff_mul_comm] at h
    exact h.symm
  have hall : Subgroup.closure (Set.range f)≤
      (Subgroup.centralizer (q '' (Subgroup.closure (Set.range g) : Set G))).comap q := by
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨i,rfl⟩
    apply Subgroup.mem_centralizer_iff.mpr
    rintro _ ⟨x,hx,rfl⟩
    exact Subgroup.mem_centralizer_singleton_iff.mp (hlocal i hx)
  apply Subgroup.commutator_le.mpr
  intro x hx y hy
  apply (QuotientGroup.eq_one_iff ⁅x,y⁆).mp
  change q ⁅x,y⁆=1
  rw [map_commutatorElement,commutatorElement_eq_one_iff_mul_comm]
  exact (Subgroup.mem_centralizer_iff.mp (hall hx) (q y) ⟨y,hy,rfl⟩).symm

end SymmetricSubgroupAsymptotics
