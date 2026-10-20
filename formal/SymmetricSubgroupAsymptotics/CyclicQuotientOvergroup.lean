import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic
import Mathlib.GroupTheory.QuotientGroup.Basic

/-! Every intermediate subgroup above a cyclic quotient kernel is normal,
and its actual quotient is cyclic. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics

variable {G : Type} [Group G] (B K : Subgroup G) [B.Normal] [IsCyclic (G⧸B)]

theorem normal_of_cyclic_quotient_kernel (hBK : B≤K) : K.Normal := by
  let q : G →* G⧸B := QuotientGroup.mk' B
  letI : CommGroup (G⧸B) := IsCyclic.commGroup
  have hmap : (K.map q).Normal := inferInstance
  have hcomap : ((K.map q).comap q).Normal := hmap.comap q
  have hker : q.ker≤K := by rw [QuotientGroup.ker_mk']; exact hBK
  rw [Subgroup.comap_map_eq_self hker] at hcomap
  exact hcomap

theorem cyclic_quotient_of_kernel_le (hBK : B≤K) :
    letI := normal_of_cyclic_quotient_kernel B K hBK
    IsCyclic (G⧸K) := by
  letI := normal_of_cyclic_quotient_kernel B K hBK
  let f : G⧸B →* G⧸K := QuotientGroup.lift B (QuotientGroup.mk' K)
    (by rw [QuotientGroup.ker_mk']; exact hBK)
  have hf : Function.Surjective f := by
    intro y
    obtain ⟨x,rfl⟩ := QuotientGroup.mk'_surjective K y
    exact ⟨QuotientGroup.mk' B x,rfl⟩
  exact isCyclic_of_surjective f hf

end SymmetricSubgroupAsymptotics
