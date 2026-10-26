import Mathlib.GroupTheory.GroupAction.ConjAct
import Mathlib.GroupTheory.OrderOfElement
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Group
import Mathlib.Tactic.NormNum

/-! Inner conjugation by an involution normalizes its literal two-sided
subgroup intersection. Normalization of a cyclic order-four subgroup
fixes its generator square. Only four scalar powers are considered. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CyclicFourInvolutionIntersection
variable {G : Type*} [Group G]

private theorem conjugate_twice (w x : G) (hw : w^2=1) :
    w*(w*x*w⁻¹)*w⁻¹=x := by
  have hi : w⁻¹=w := inv_eq_of_mul_eq_one_right ((pow_two w).symm.trans hw)
  have hww : w*w=1 := (pow_two w).symm.trans hw
  calc
    _=(w*w)*x*(w*w) := by rw [hi]; group
    _=x := by rw [hww,one_mul,mul_one]

theorem normalizes_intersection (U : Subgroup G) (w : G) (hw : w^2=1) :
    w∈Subgroup.normalizer (U⊓U.comap (MulAut.conj w).toMonoidHom : Set G) := by
  intro x
  change (x∈U ∧ w*x*w⁻¹∈U) ↔
    (w*x*w⁻¹∈U ∧ w*(w*x*w⁻¹)*w⁻¹∈U)
  rw [conjugate_twice w x hw]
  exact and_comm

theorem square_fixed_of_normalizes [Finite G] (y w : G) (hy : orderOf y=4)
    (hw : w∈Subgroup.normalizer (Subgroup.zpowers y : Set G)) :
    w*y^2*w⁻¹=y^2 := by
  classical
  let F : MulAut G := MulAut.conj w
  have hm : F y∈Subgroup.zpowers y :=
    (hw y).mp (Subgroup.mem_zpowers y)
  obtain ⟨k,hk,he⟩ := Finset.mem_image.mp (mem_zpowers_iff_mem_range_orderOf.mp hm)
  have hk4 : k<4 := by simpa only [hy] using Finset.mem_range.mp hk
  have hy4 : y^4=1 := by rw [←hy]; exact pow_orderOf_eq_one y
  have hy2 : y^2≠1 := by
    intro h
    have hd := orderOf_dvd_of_pow_eq_one h
    rw [hy] at hd
    norm_num at hd
  have hk0 : k≠0 := by
    intro h
    have hf : F y=1 := he.symm.trans (by rw [h,pow_zero])
    have hy1 : y=1 := F.injective (hf.trans (map_one F).symm)
    exact hy2 (by rw [hy1,one_pow])
  have hk2 : k≠2 := by
    intro h
    have hf : F (y^2)=1 := by
      rw [map_pow,←he,h,←pow_mul]
      exact hy4
    exact hy2 (F.injective (hf.trans (map_one F).symm))
  have hodd : k=1 ∨ k=3 := by omega
  change F (y^2)=y^2
  rw [map_pow,←he,←pow_mul]
  rcases hodd with rfl | rfl
  · simp only [one_mul]
  · calc
      y^(3*2)=y^4*y^2 := (pow_add y 4 2)
      _=y^2 := by rw [hy4,one_mul]

end SymmetricSubgroupAsymptotics.CyclicFourInvolutionIntersection
