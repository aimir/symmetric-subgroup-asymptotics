import SymmetricSubgroupAsymptotics.Non2SchurMixedSocleDimension
import SymmetricSubgroupAsymptotics.Non2SchurScalarOrbit
import SymmetricSubgroupAsymptotics.SemisimpleModuleGenerators

/-! Two generator positions from actual cubic projectors. A cyclic
order-three action with fixed dimension at most two and nonfixed binary
dimension at most four has Schur capacity at most two. The density uses
the NONFIXED projector image, not the larger total dimension. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped MonoidAlgebra
namespace SymmetricSubgroupAsymptotics.CubicProjectorSchurCapacity

variable {H V : Type} [Group H] [Finite H] [AddCommGroup V]
  [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]

omit [FiniteDimensional (ZMod 2) V] in
private theorem add_self (x : V) : x+x=0 := by
  rw [← two_smul (ZMod 2),show (2 : ZMod 2)=0 by decide,zero_smul]

theorem capacity_le_two (sigma : Representation (ZMod 2) H V) (a : H)
    (hgen : ∀ g : H, ∃ n : ℕ, g=a^n) (hcube : (sigma a)^3=1)
    (hfixed : Module.finrank (ZMod 2) sigma.invariants≤2)
    (hactive : Module.finrank (ZMod 2) (LinearMap.range (sigma a+(sigma a)^2))≤4) :
    representationSchurCapacity sigma≤2 := by
  apply (representationSchurCapacity_le_max_fixed_nontrivial sigma 2 ?_).trans
    (max_le (by exact_mod_cast hfixed) le_rfl)
  intro S hS hnon
  letI : IsSimpleModule (ZMod 2)[H] S := hS
  letI : FiniteDimensional (ZMod 2) S := FiniteDimensional.of_injective
    (S.subtype.restrictScalars (ZMod 2)) S.subtype_injective
  let A := sigma a
  let E : Module.End (ZMod 2) V := 1+A+A^2
  let F : Module.End (ZMod 2) V := A+A^2
  have hAE : ∀ v, A (E v)=E v := by
    intro v
    change A (v+A v+A (A v))=v+A v+A (A v)
    rw [map_add,map_add]
    have hh : A (A (A v))=v := congrArg (fun f : Module.End (ZMod 2) V => f v) hcube
    rw [hh]
    abel
  have hEF : ∀ (g : H) v, sigma g (E v)=E v := by
    intro g v
    obtain ⟨n,rfl⟩ := hgen g
    rw [map_pow]
    change (A^n) (E v)=E v
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [pow_succ',Module.End.mul_apply,ih,hAE]
  let P := isotypicComponent (ZMod 2)[H] sigma.asModule S
  let e : (ZMod 2)[H] := 1+MonoidAlgebra.single a 1+(MonoidAlgebra.single a 1)^2
  have he : sigma.asAlgebraHom e=E := by
    simp only [e,E,A,map_add,map_one,map_pow,Representation.asAlgebraHom_single_one]
  have hmem : ∀ y : P, sigma.asModuleEquiv (y : sigma.asModule)∈F.range := by
    intro y
    let x : P := ⟨e • (y : sigma.asModule),P.smul_mem e y.property⟩
    have hx : x=0 := isotypicComponent_fixed_eq_zero_of_nonfixed sigma S hnon x (by
      intro g
      apply Subtype.ext
      apply sigma.asModuleEquiv.injective
      change sigma.asModuleEquiv (MonoidAlgebra.single g 1 • (e • (y : sigma.asModule)))=
        sigma.asModuleEquiv (e • (y : sigma.asModule))
      simp only [Representation.asModuleEquiv_map_smul,Representation.asAlgebraHom_single_one]
      rw [he]
      exact hEF g _)
    have hxzero : E (sigma.asModuleEquiv (y : sigma.asModule))=0 := by
      have hh := congrArg (fun z : P => sigma.asModuleEquiv (z : sigma.asModule)) hx
      change sigma.asModuleEquiv (e • (y : sigma.asModule))=sigma.asModuleEquiv 0 at hh
      rw [Representation.asModuleEquiv_map_smul,he,map_zero] at hh
      exact hh
    let v := sigma.asModuleEquiv (y : sigma.asModule)
    have hv : F v=v := by
      have hh : v+F v=0 := by
        simpa only [E,F,LinearMap.add_apply,Module.End.one_apply,add_assoc] using hxzero
      exact add_left_cancel (hh.trans (add_self v).symm)
    exact ⟨v,hv⟩
  let f : (P.restrictScalars (ZMod 2)) →ₗ[ZMod 2] V :=
    sigma.asModuleEquiv.toLinearMap.comp (P.subtype.restrictScalars (ZMod 2))
  let fR := f.codRestrict F.range hmem
  have hfR : Function.Injective fR := by
    intro x y h
    apply Subtype.ext
    apply sigma.asModuleEquiv.injective
    exact congrArg (fun z : F.range => (z : V)) h
  have hdim : Module.finrank (ZMod 2) (P.restrictScalars (ZMod 2))≤4 :=
    (fR.finrank_le_finrank_of_injective hfR).trans hactive
  have hoccupied : Module.finrank (ZMod 2) S *
      schurSocleMultiplicity (k := ZMod 2) (R := (ZMod 2)[H])
        (A := sigma.asModule) (X := S)≤4 := by
    rw [← schur_isotypic_finrank_eq sigma S]
    exact hdim
  let density : ℝ :=
    (Module.finrank (ZMod 2) (S →ₗ[(ZMod 2)[H]] sigma.asModule) : ℝ) /
      Module.finrank (ZMod 2) S
  have htwo : (2 : ℝ)≤schurSimpleProductDegree sigma S := by
    exact_mod_cast two_le_schurSimpleProductDegree_of_nonfixed sigma S hnon
  have hnonneg : 0≤density := schurSimpleRatio_nonneg sigma S
  have hproduct : (schurSimpleProductDegree sigma S : ℝ)*density≤4 := by
    change (schurSimpleProductDegree sigma S : ℝ)*
      ((Module.finrank (ZMod 2) (S →ₗ[(ZMod 2)[H]] sigma.asModule) : ℝ) /
        Module.finrank (ZMod 2) S)≤4
    rw [schurSimpleProductDegree_mul_ratio sigma S 0]
    simp only [schurMixedSocleDimension,zero_add,Nat.cast_zero,sub_zero]
    exact_mod_cast hoccupied
  change density≤2
  nlinarith [mul_nonneg (sub_nonneg.mpr htwo) hnonneg]

theorem generatedBy_two (sigma : Representation (ZMod 2) H V)
    [IsSemisimpleModule (ZMod 2)[H] sigma.asModule] (a : H)
    (hgen : ∀ g : H, ∃ n : ℕ, g=a^n) (hcube : (sigma a)^3=1)
    (hfixed : Module.finrank (ZMod 2) sigma.invariants≤2)
    (hactive : Module.finrank (ZMod 2) (LinearMap.range (sigma a+(sigma a)^2))≤4) :
    RepresentationGeneratedBy sigma 2 :=
  semisimple_representationGeneratedBy_of_schurCapacity_le sigma 2
    (capacity_le_two sigma a hgen hcube hfixed hactive)

end SymmetricSubgroupAsymptotics.CubicProjectorSchurCapacity
