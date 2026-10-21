import Mathlib.LinearAlgebra.Transvection.Basic
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.Tactic.Abel

/-! Centre/axis geometry of actual transvections. These are linear-map
identities, not an assertion that an arbitrary abstract PSL automorphism
preserves transvections. The latter recognition remains a separate step. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTypeATransvectionGeometry
open Module LinearMap Submodule
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

def displacement (f : Dual K V) (v : V) : V→ₗ[K]V :=
  LinearMap.transvection f v-LinearMap.id

@[simp] theorem displacement_apply (f : Dual K V) (v x : V) :
    displacement f v x=f x • v := by
  simp [displacement,LinearMap.transvection.apply]

private theorem exists_nonzero_value {f : Dual K V} (hf : f≠0) :
    ∃x,f x≠0 := by
  by_contra h
  simp only [not_exists,not_not] at h
  apply hf
  ext x
  exact h x

/-- The nonzero form gives the original centre line of a transvection. -/
theorem displacement_range {f : Dual K V} (hf : f≠0) (v : V) :
    LinearMap.range (displacement f v)=K ∙ v := by
  apply le_antisymm
  · rintro y ⟨x,rfl⟩
    rw [displacement_apply]
    exact (K ∙ v).smul_mem _ (Submodule.mem_span_singleton_self v)
  · intro y hy
    obtain ⟨a,rfl⟩ := Submodule.mem_span_singleton.mp hy
    obtain ⟨x,hx⟩ := exists_nonzero_value hf
    refine ⟨(a/f x) • x,?_⟩
    simp only [displacement_apply,map_smul,smul_smul,div_mul_cancel₀ _ hx]

/-- The nonzero vector gives the original fixed hyperplane. -/
theorem displacement_ker (f : Dual K V) {v : V} (hv : v≠0) :
    LinearMap.ker (displacement f v)=LinearMap.ker f := by
  ext x
  simp only [LinearMap.mem_ker,displacement_apply,smul_eq_zero,hv,or_false]

theorem centre_eq_of_transvection_eq {f g : Dual K V} {v w : V}
    (hf : f≠0) (hg : g≠0) (he : LinearMap.transvection f v=LinearMap.transvection g w) :
    K ∙ v=K ∙ w := by
  have hd : displacement f v=displacement g w := congrArg (fun t => t-LinearMap.id) he
  rw [←displacement_range hf,←displacement_range hg,hd]

theorem axis_eq_of_transvection_eq {f g : Dual K V} {v w : V}
    (hv : v≠0) (hw : w≠0) (he : LinearMap.transvection f v=LinearMap.transvection g w) :
    LinearMap.ker f=LinearMap.ker g := by
  have hd : displacement f v=displacement g w := congrArg (fun t => t-LinearMap.id) he
  rw [←displacement_ker f hv,←displacement_ker g hw,hd]

theorem transvection_product_apply (f g : Dual K V) (v w x : V) :
    LinearMap.transvection f v (LinearMap.transvection g w x)=
      (x+f x • v+g x • w)+(g x*f w) • v := by
  simp only [LinearMap.transvection.apply,map_add,map_smul,add_smul,smul_add,smul_smul]
  abel

/-- Commuting is precisely the equality of the two rank-one cross terms. -/
theorem transvection_comp_commute_iff (f g : Dual K V) (v w : V) :
    (LinearMap.transvection f v).comp (LinearMap.transvection g w)=
      (LinearMap.transvection g w).comp (LinearMap.transvection f v) ↔
      ∀x,(g x*f w) • v=(f x*g v) • w := by
  constructor
  · intro he x
    have hx := congrArg (fun t : V→ₗ[K]V => t x) he
    simp only [LinearMap.comp_apply,transvection_product_apply] at hx
    have hx' : (x+f x • v+g x • w)+(g x*f w) • v=
        (x+f x • v+g x • w)+(f x*g v) • w := by
      calc
        _=(x+g x • w+f x • v)+(f x*g v) • w := hx
        _=_ := by abel
    exact add_left_cancel hx'
  · intro he
    ext x
    simp only [LinearMap.comp_apply,transvection_product_apply]
    rw [he x]
    abel

/-- For distinct centre points, commuting detects the two incidences
between each centre and the other transvection's fixed hyperplane. -/
theorem transvection_comp_commute_iff_incident {f g : Dual K V} {v w : V}
    (hf : f≠0) (hg : g≠0) (hi : LinearIndependent K ![v,w]) :
    (LinearMap.transvection f v).comp (LinearMap.transvection g w)=
      (LinearMap.transvection g w).comp (LinearMap.transvection f v) ↔
      f w=0 ∧ g v=0 := by
  rw [transvection_comp_commute_iff]
  constructor
  · intro he
    have hz (x : V) : g x*f w=0 ∧ -(f x*g v)=0 := by
      apply (LinearIndependent.pair_iff.mp hi)
      rw [neg_smul,add_neg_eq_zero]
      exact he x
    obtain ⟨x,hx⟩ := exists_nonzero_value hf
    obtain ⟨y,hy⟩ := exists_nonzero_value hg
    exact ⟨(mul_eq_zero.mp (hz y).1).resolve_left hy,
      (mul_eq_zero.mp (neg_eq_zero.mp (hz x).2)).resolve_left hx⟩
  · rintro ⟨hfw,hgv⟩ x
    simp only [hfw,hgv,mul_zero,zero_smul]

end SymmetricSubgroupAsymptotics.CFSGTypeATransvectionGeometry
