import Mathlib.RingTheory.SimpleModule.Isotypic
import Mathlib.LinearAlgebra.Projection
import Mathlib.RingTheory.Finiteness.Basic

/-! Finite semisimple double-centralizer density makes the projection
onto a fully invariant summand an actual scalar action. This supplies
simultaneous generator-slot sharing across distinct socle isotypic types. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics

theorem central_endomorphism_scalar
    {R M : Type} [Ring R] [AddCommGroup M] [Module R M] [Finite M]
    [IsSemisimpleModule R M] (p : Module.End R M)
    (hp : ∀ f : Module.End R M, p*f=f*p) :
    ∃ r : R, ∀ x : M, r • x=p x := by
  letI : Module.Finite (Module.End R M) M := Module.Finite.of_finite
  let F : Module.End (Module.End R M) M := {
    toFun := p
    map_add' := p.map_add
    map_smul' := by
      intro f x
      change p (f x)=f (p x)
      exact congrArg (fun q : Module.End R M => q x) (hp f) }
  have hs : Function.Surjective
      (Module.toModuleEnd (Module.End R M) (S := R) M) :=
    Module.Finite.toModuleEnd_moduleEnd_surjective
  obtain ⟨r,hr⟩ := hs F
  exact ⟨r,fun x => LinearMap.congr_fun hr x⟩

/-- Projections onto fully invariant complementary summands commute with
every module endomorphism and are therefore actual scalar operations. -/
theorem scalar_projection_of_fullyInvariant_complement
    {R M : Type} [Ring R] [AddCommGroup M] [Module R M] [Finite M]
    [IsSemisimpleModule R M] (P Q : Submodule R M)
    (hPQ : IsCompl P Q) (hP : P.IsFullyInvariant) (hQ : Q.IsFullyInvariant) :
    ∃ r : R, (∀ x∈P, r • x=x) ∧ (∀ x∈Q, r • x=0) := by
  let p : Module.End R M := P.subtype.comp (P.projectionOnto Q hPQ)
  have hleft (x : M) (hx : x∈P) : p x=x := by
    exact congrArg Subtype.val (Submodule.projectionOnto_apply_left hPQ ⟨x,hx⟩)
  have hright (x : M) (hx : x∈Q) : p x=0 := by
    have h := Submodule.projectionOnto_apply_of_mem_right hPQ hx
    exact congrArg Subtype.val h
  have hcentral : ∀ f : Module.End R M, p*f=f*p := by
    intro f
    apply LinearMap.ext
    intro x
    have hx : x∈P⊔Q := by rw [hPQ.sup_eq_top]; trivial
    obtain ⟨y,hy,z,hz,rfl⟩ := Submodule.mem_sup.mp hx
    change p (f (y+z))=f (p (y+z))
    calc
      p (f (y+z)) = p (f y+f z) := congrArg p (f.map_add y z)
      _ = f y := by rw [p.map_add,hleft _ (hP f hy),hright _ (hQ f hz),add_zero]
      _ = f (p (y+z)) := by rw [p.map_add,hleft y hy,hright z hz,add_zero]
  obtain ⟨r,hr⟩ := central_endomorphism_scalar p hcentral
  exact ⟨r,fun x hx => (hr x).trans (hleft x hx),
    fun x hx => (hr x).trans (hright x hx)⟩

end SymmetricSubgroupAsymptotics
