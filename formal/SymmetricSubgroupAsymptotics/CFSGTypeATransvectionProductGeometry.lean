import SymmetricSubgroupAsymptotics.CFSGTypeATransvectionGeometry
import Mathlib.LinearAlgebra.Dual.Lemmas
import Lean.Elab.Tactic.Omega

/-! If a product of two nonidentity rank-one transvections is again a
rank-one transvection, their centre lines or their fixed hyperplanes
agree. This is the concrete linear-algebra step behind root-star and
root-costar recognition. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTypeATransvectionProductGeometry
open Module LinearMap Submodule CFSGTypeATransvectionGeometry
variable {F V : Type*} [Field F] [AddCommGroup V] [Module F V] [FiniteDimensional F V]

omit [FiniteDimensional F V] in
private theorem exists_nonzero_value {f : Dual F V} (hf : f≠0) : ∃x,f x≠0 := by
  by_contra h
  simp only [not_exists,not_not] at h
  apply hf
  apply LinearMap.ext
  intro x
  exact h x

theorem product_transvection_independent_centres_equal_axes
    {f g h : Dual F V} {v w u : V} (hf : f≠0) (hg : g≠0)
    (hi : LinearIndependent F ![v,w])
    (he : (LinearMap.transvection f v).comp (LinearMap.transvection g w)=LinearMap.transvection h u) :
    LinearMap.ker f=LinearMap.ker g := by
  by_contra hne
  have hv : v≠0 := by simpa using hi.ne_zero (0 : Fin 2)
  have hnot : ¬LinearMap.ker g≤LinearMap.ker f := by
    intro hle
    have hdf := Module.Dual.finrank_ker_add_one_of_ne_zero hf
    have hdg := Module.Dual.finrank_ker_add_one_of_ne_zero hg
    exact hne (Submodule.eq_of_le_of_finrank_le hle (by omega)).symm
  obtain ⟨x,hgx,hfx⟩ : ∃x,g x=0 ∧ f x≠0 := by
    by_contra hn
    apply hnot
    intro x hx
    change f x=0
    by_contra hfx
    exact hn ⟨x,hx,hfx⟩
  have hvec : f x • v=h x • u := by
    have hh := congrArg (fun t : V→ₗ[F]V => t x) he
    simp only [LinearMap.comp_apply,LinearMap.transvection.apply,hgx,zero_smul,add_zero] at hh
    exact add_left_cancel hh
  have hhx : h x≠0 := by
    intro hhx
    rw [hhx,zero_smul] at hvec
    exact (smul_ne_zero hfx hv) hvec
  have huspan : u∈F ∙ v := by
    apply ((F ∙ v).smul_mem_iff hhx).mp
    rw [←hvec]
    exact (F ∙ v).smul_mem _ (Submodule.mem_span_singleton_self v)
  obtain ⟨y,hgy⟩ := exists_nonzero_value hg
  have hm : f y • v+g y • w+(g y*f w) • v∈F ∙ v := by
    have hh := congrArg (fun t : V→ₗ[F]V => t y) he
    simp only [LinearMap.comp_apply] at hh
    rw [transvection_product_apply,LinearMap.transvection.apply] at hh
    have hdisp : f y • v+g y • w+(g y*f w) • v=h y • u := by
      have ht : y+(f y • v+g y • w+(g y*f w) • v)=y+h y • u := by
        calc
          _=(y+f y • v+g y • w)+(g y*f w) • v := by abel
          _=y+h y • u := hh
      exact add_left_cancel ht
    rw [hdisp]
    exact (F ∙ v).smul_mem _ huspan
  have hcross : (g y*f w) • v∈F ∙ v :=
    (F ∙ v).smul_mem _ (Submodule.mem_span_singleton_self v)
  have hfirst : f y • v∈F ∙ v :=
    (F ∙ v).smul_mem _ (Submodule.mem_span_singleton_self v)
  have hsub := (F ∙ v).sub_mem ((F ∙ v).sub_mem hm hcross) hfirst
  have heq : ((f y • v+g y • w+(g y*f w) • v)-(g y*f w) • v)-f y • v=g y • w := by abel
  rw [heq] at hsub
  have hwspan : w∈F ∙ v := ((F ∙ v).smul_mem_iff hgy).mp hsub
  obtain ⟨a,ha⟩ := Submodule.mem_span_singleton.mp hwspan
  exact (LinearIndependent.pair_iff' hv).mp hi a ha

theorem product_transvection_common_centre_or_axis
    {f g h : Dual F V} {v w u : V} (hf : f≠0) (hg : g≠0) (hv : v≠0) (hw : w≠0)
    (he : (LinearMap.transvection f v).comp (LinearMap.transvection g w)=LinearMap.transvection h u) :
    (F ∙ v)=(F ∙ w) ∨ LinearMap.ker f=LinearMap.ker g := by
  by_cases hc : (F ∙ v)=(F ∙ w)
  · exact Or.inl hc
  · right
    apply product_transvection_independent_centres_equal_axes hf hg ?_ he
    apply (LinearIndependent.pair_iff' hv).mpr
    intro a ha
    have ha0 : a≠0 := by
      intro ha0
      rw [ha0,zero_smul] at ha
      exact hw ha.symm
    apply hc
    apply Submodule.span_singleton_eq_span_singleton.mpr
    exact ⟨Units.mk0 a ha0,ha⟩

end SymmetricSubgroupAsymptotics.CFSGTypeATransvectionProductGeometry
