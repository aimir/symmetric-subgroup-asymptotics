import SymmetricSubgroupAsymptotics.RepresentationNestedQuotientFixedExtension

/-!
# Removing fixed lower layers from a nested quotient

If `A ≤ C ≤ B` and every displacement of `C` lies in `A`, the kernel
`C/A` of `B/A → B/C` is pointwise fixed. Postcomposition with this map is
injective on maps from any nonfixed simple source. Thus removing the lower
layer cannot decrease the nonfixed Schur multiplicity. The same statement
holds after pullback along an arbitrary group homomorphism.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped MonoidAlgebra

namespace SymmetricSubgroupAsymptotics

variable {k G V W X : Type} [Field k] [Group G]
  [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]
  [AddCommGroup X] [Module k X]

/-- An intertwiner with pointwise fixed kernel induces an injection on
maps from a nonfixed simple source, and hence a Schur multiplicity bound.
The intertwiner need not be surjective. -/
theorem schurSocleMultiplicity_le_of_nonfixed_fixed_kernel
    [FiniteDimensional k V] [FiniteDimensional k W]
    (sigma : Representation k G X) (S : Submodule k[G] sigma.asModule)
    [FiniteDimensional k S] [IsSimpleModule k[G] S]
    (hnonfixed : ¬ representationSubmoduleFixed sigma S)
    (rho : Representation k G V) (tau : Representation k G W)
    (q : rho.IntertwiningMap tau)
    (hkernel : ∀ g v, q v = 0 → rho g v = v) :
    schurSocleMultiplicity (k := k) (R := k[G]) (A := rho.asModule) (X := S) ≤
      schurSocleMultiplicity (k := k) (R := k[G]) (A := tau.asModule) (X := S) := by
  let qR : rho.asModule →ₗ[k[G]] tau.asModule :=
    Representation.IntertwiningMap.equivLinearMapAsModule rho tau q
  let post : (S →ₗ[k[G]] rho.asModule) →ₗ[k]
      (S →ₗ[k[G]] tau.asModule) :=
    { toFun := fun f ↦ qR.comp f
      map_add' := by intro f g; ext x; exact qR.map_add (f x) (g x)
      map_smul' := by intro c f; ext x; exact (qR.restrictScalars k).map_smul c (f x) }
  have hzero (f : S →ₗ[k[G]] rho.asModule) (hf : post f = 0) : f = 0 := by
    by_contra hne
    have hfinj : Function.Injective f := LinearMap.injective_of_ne_zero hne
    apply hnonfixed
    intro g y
    apply hfinj
    apply rho.asModuleEquiv.injective
    rw [f.map_smul, Representation.asModuleEquiv_map_smul,
      Representation.asAlgebraHom_single, one_smul]
    apply hkernel g
    have hy := LinearMap.congr_fun hf y
    change q (rho.asModuleEquiv (f y)) = 0 at hy
    exact hy
  have hpost : Function.Injective post := by
    intro f g hfg
    apply sub_eq_zero.mp
    apply hzero
    rw [map_sub, hfg, sub_self]
  have hhom := post.finrank_le_finrank_of_injective hpost
  rw [schurHom_finrank_eq_multiplicity
        (k := k) (R := k[G]) (A := rho.asModule) (X := S),
    schurHom_finrank_eq_multiplicity
        (k := k) (R := k[G]) (A := tau.asModule) (X := S)] at hhom
  apply Nat.le_of_mul_le_mul_right hhom
  letI : Nontrivial S := IsSimpleModule.nontrivial k[G] S
  exact Module.finrank_pos (R := k) (M := Module.End k[G] S)

/-- The quotient map obtained by enlarging the lower state from `A` to
`C`, with the same literal numerator `B`. -/
def nestedQuotientLowerProjection
    {rho : Representation k G V} (A C B : Subrepresentation rho)
    (hAC : A ≤ C) (hCB : C ≤ B) :
    (nestedQuotientRepresentation A B (hAC.trans hCB)).IntertwiningMap
      (nestedQuotientRepresentation C B hCB) where
  toLinearMap := (nestedSubrepresentation A B (hAC.trans hCB)).toSubmodule.liftQ
    (nestedSubrepresentation C B hCB).toSubmodule.mkQ (by
      intro v hv
      exact (Submodule.Quotient.mk_eq_zero _).mpr (hAC hv))
  isIntertwining' := by
    intro g
    apply LinearMap.ext
    intro z
    obtain ⟨v, rfl⟩ :=
      (nestedSubrepresentation A B (hAC.trans hCB)).toSubmodule.mkQ_surjective z
    rfl

/-- Displacements of `C` in `A` make the kernel of `B/A → B/C`
pointwise fixed. -/
theorem nestedQuotientLowerProjection_fixed_kernel
    {rho : Representation k G V} (A C B : Subrepresentation rho)
    (hAC : A ≤ C) (hCB : C ≤ B)
    (hdisplacements : ∀ g v, v ∈ C → rho g v - v ∈ A)
    (g : G)
    (z : B.toSubmodule ⧸
      (nestedSubrepresentation A B (hAC.trans hCB)).toSubmodule)
    (hz : nestedQuotientLowerProjection A C B hAC hCB z = 0) :
    nestedQuotientRepresentation A B (hAC.trans hCB) g z = z := by
  obtain ⟨v, rfl⟩ :=
    (nestedSubrepresentation A B (hAC.trans hCB)).toSubmodule.mkQ_surjective z
  have hvC : v.1 ∈ C :=
    (Submodule.Quotient.mk_eq_zero
      (nestedSubrepresentation C B hCB).toSubmodule).mp hz
  change (nestedSubrepresentation A B (hAC.trans hCB)).toSubmodule.mkQ
      (B.toRepresentation g v) =
    (nestedSubrepresentation A B (hAC.trans hCB)).toSubmodule.mkQ v
  apply (Submodule.Quotient.eq
    (nestedSubrepresentation A B (hAC.trans hCB)).toSubmodule).mpr
  exact hdisplacements g v.1 hvC

/-- Removing a fixed lower layer bounds every nonfixed simple-source
Schur multiplicity, also after pullback along any group homomorphism. -/
theorem nestedQuotient_comp_nonfixed_le_of_lower_displacements
    [FiniteDimensional k V]
    {H : Type} [Group H] (gamma : H →* G)
    {rho : Representation k G V} (A C B : Subrepresentation rho)
    (hAC : A ≤ C) (hCB : C ≤ B)
    (hdisplacements : ∀ g v, v ∈ C → rho g v - v ∈ A)
    (sigma : Representation k H X) (S : Submodule k[H] sigma.asModule)
    [FiniteDimensional k S] [IsSimpleModule k[H] S]
    (hnonfixed : ¬ representationSubmoduleFixed sigma S) :
    schurSocleMultiplicity (k := k) (R := k[H])
        (A := (inflatedRepresentation gamma
          (nestedQuotientRepresentation A B (hAC.trans hCB))).asModule)
        (X := S) ≤
      schurSocleMultiplicity (k := k) (R := k[H])
        (A := (inflatedRepresentation gamma
          (nestedQuotientRepresentation C B hCB)).asModule)
        (X := S) := by
  let tau := inflatedRepresentation gamma
    (nestedQuotientRepresentation A B (hAC.trans hCB))
  let nu := inflatedRepresentation gamma (nestedQuotientRepresentation C B hCB)
  let q : tau.IntertwiningMap nu :=
    { toLinearMap := (nestedQuotientLowerProjection A C B hAC hCB).toLinearMap
      isIntertwining' := fun g ↦
        (nestedQuotientLowerProjection A C B hAC hCB).isIntertwining' (gamma g) }
  apply schurSocleMultiplicity_le_of_nonfixed_fixed_kernel
    sigma S hnonfixed tau nu q
  intro g z hz
  exact nestedQuotientLowerProjection_fixed_kernel A C B hAC hCB
    hdisplacements (gamma g) z hz

end SymmetricSubgroupAsymptotics

end
