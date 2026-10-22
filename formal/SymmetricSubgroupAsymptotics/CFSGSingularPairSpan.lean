import SymmetricSubgroupAsymptotics.CFSGTwoDimensionalCompanion
import Mathlib.LinearAlgebra.BilinearForm.Basic

/-! Dimension and bilinear singularity of the span of a literal pair. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGSingularPairSpan
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem finrank_pair (u w : V) (hu : u≠0) (hi : ∀ c:K,w≠c•u) :
    Module.finrank K (Submodule.span K {u,w})=2 := by
  classical
  have hlin : LinearIndependent K ![u,w] :=
    (LinearIndependent.pair_iff' hu).mpr (fun c h=>hi c h.symm)
  have hr : Set.range ![u,w]=({u,w}:Set V) := by
    ext x
    constructor
    · rintro ⟨i,rfl⟩
      fin_cases i <;> simp
    · rintro (hx|hx)
      · exact ⟨0,hx.symm⟩
      · exact ⟨1,(Set.mem_singleton_iff.mp hx).symm⟩
  have hd := finrank_span_eq_card hlin
  rw [hr,Fintype.card_fin] at hd
  exact hd

theorem zeroOn_pair (B : LinearMap.BilinForm K V) (u w : V)
    (huu : B u u=0) (huw : B u w=0) (hwu : B w u=0) (hww : B w w=0) :
    ∀x∈Submodule.span K {u,w},∀y∈Submodule.span K {u,w},B x y=0 := by
  intro x hx y hy
  obtain ⟨a,b,rfl⟩ := Submodule.mem_span_pair.mp hx
  obtain ⟨c,d,rfl⟩ := Submodule.mem_span_pair.mp hy
  simp only [map_add,map_smul,LinearMap.add_apply,LinearMap.smul_apply,
    huu,huw,hwu,hww,smul_zero,add_zero]

theorem zeroOn_sup (B : LinearMap.BilinForm K V)
    (hs : ∀x y,B x y=B y x) (P Q : Submodule K V)
    (hP : ∀x∈P,∀y∈P,B x y=0) (hQ : ∀x∈Q,∀y∈Q,B x y=0)
    (hc : ∀x∈P,∀y∈Q,B x y=0) : ∀x∈P⊔Q,∀y∈P⊔Q,B x y=0 := by
  intro x hx y hy
  obtain ⟨p,hp,q,hq,rfl⟩ := Submodule.mem_sup.mp hx
  obtain ⟨p',hp',q',hq',rfl⟩ := Submodule.mem_sup.mp hy
  have hrev : B q p'=0 := (hs q p').trans (hc p' hp' q hq)
  simp only [map_add,LinearMap.add_apply,hP p hp p' hp',hc p hp q' hq',
    hrev,hQ q hq q' hq',add_zero]

end SymmetricSubgroupAsymptotics.CFSGSingularPairSpan
