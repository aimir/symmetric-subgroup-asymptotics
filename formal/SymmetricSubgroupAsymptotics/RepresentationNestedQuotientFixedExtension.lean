import SymmetricSubgroupAsymptotics.NonfixedCoinvariantKernel
import SymmetricSubgroupAsymptotics.RepresentationSelfDualNestedQuotient

/-!
# Removing fixed layers from a nested quotient

If `A ≤ C ≤ B` and every displacement of `B` lies in `C`, every nonfixed
simple-source map into `B/A` factors through `C/A`. Consequently the larger
quotient has no greater nonfixed Schur multiplicity. This remains true after
pullback along any group homomorphism; no splitting is used.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped MonoidAlgebra

namespace SymmetricSubgroupAsymptotics

variable {k G V W X : Type} [Field k] [Group G]
  [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]
  [AddCommGroup X] [Module k X]

/-- An injective intertwiner containing all displacements contains every
nonfixed simple-source map. -/
theorem schurSocleMultiplicity_le_of_nonfixed_displacements
    [FiniteDimensional k V] [FiniteDimensional k W]
    (sigma : Representation k G X) (S : Submodule k[G] sigma.asModule)
    [FiniteDimensional k S] [IsSimpleModule k[G] S]
    (hnonfixed : ¬ representationSubmoduleFixed sigma S)
    (rho : Representation k G V) (tau : Representation k G W)
    (i : tau.IntertwiningMap rho) (hi : Function.Injective i)
    (hdisplacements : Representation.Coinvariants.ker rho ≤
      LinearMap.range i.toLinearMap) :
    schurSocleMultiplicity (k := k) (R := k[G]) (A := rho.asModule) (X := S) ≤
      schurSocleMultiplicity (k := k) (R := k[G]) (A := tau.asModule) (X := S) := by
  let e := LinearEquiv.ofInjective i.toLinearMap hi
  let K := representationCoinvariantsKernelSubrepresentation rho
  let toRange : K.toSubmodule →ₗ[k] LinearMap.range i.toLinearMap :=
    { toFun := fun v ↦ ⟨v.1, hdisplacements v.2⟩
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  let j : K.toRepresentation.IntertwiningMap tau :=
    { toLinearMap := e.symm.toLinearMap.comp toRange
      isIntertwining' := by
        intro g
        apply LinearMap.ext
        intro v
        apply hi
        change i (e.symm ⟨rho g v.1, hdisplacements (K.apply_mem_toSubmodule g v.2)⟩) =
          i (tau g (e.symm ⟨v.1, hdisplacements v.2⟩))
        rw [Representation.IntertwiningMap.isIntertwining]
        have he (z : LinearMap.range i.toLinearMap) : i (e.symm z) = z.1 :=
          congrArg Subtype.val (e.apply_symm_apply z)
        rw [he, he] }
  have hj : Function.Injective j := by
    intro v w hvw
    apply Subtype.ext
    have h := congrArg (fun z ↦ i z) hvw
    change i (e.symm ⟨v.1, hdisplacements v.2⟩) =
      i (e.symm ⟨w.1, hdisplacements w.2⟩) at h
    have he (z : LinearMap.range i.toLinearMap) : i (e.symm z) = z.1 :=
      congrArg Subtype.val (e.apply_symm_apply z)
    simpa only [he] using h
  exact schurSocleMultiplicity_le_of_nonfixed_coinvariantsKernel_injection
    sigma S hnonfixed rho tau j hj

/-- The inclusion of two quotients by the same literal lower state. -/
def nestedQuotientInclusion
    {rho : Representation k G V} (A C B : Subrepresentation rho)
    (hAC : A ≤ C) (hCB : C ≤ B) :
    (nestedQuotientRepresentation A C hAC).IntertwiningMap
      (nestedQuotientRepresentation A B (hAC.trans hCB)) where
  toLinearMap := (nestedSubrepresentation A C hAC).toSubmodule.liftQ
    ((nestedSubrepresentation A B (hAC.trans hCB)).toSubmodule.mkQ.comp
      (C.toSubmodule.inclusion hCB)) (by
        intro v hv
        exact (Submodule.Quotient.mk_eq_zero _).mpr hv)
  isIntertwining' := by
    intro g
    apply LinearMap.ext
    intro x
    obtain ⟨v, rfl⟩ := (nestedSubrepresentation A C hAC).toSubmodule.mkQ_surjective x
    rfl

theorem nestedQuotientInclusion_injective
    {rho : Representation k G V} (A C B : Subrepresentation rho)
    (hAC : A ≤ C) (hCB : C ≤ B) :
    Function.Injective (nestedQuotientInclusion A C B hAC hCB) := by
  intro x y hxy
  obtain ⟨v, rfl⟩ := (nestedSubrepresentation A C hAC).toSubmodule.mkQ_surjective x
  obtain ⟨w, rfl⟩ := (nestedSubrepresentation A C hAC).toSubmodule.mkQ_surjective y
  apply (Submodule.Quotient.eq _).mpr
  have h := (Submodule.Quotient.eq
    (nestedSubrepresentation A B (hAC.trans hCB)).toSubmodule).mp hxy
  exact h

/-- Pulling back a fixed upper layer does not change its vanishing
contribution to nonfixed simple-source maps. -/
theorem nestedQuotient_comp_nonfixed_le_of_displacements
    [FiniteDimensional k V]
    {H : Type} [Group H] (gamma : H →* G)
    {rho : Representation k G V} (A C B : Subrepresentation rho)
    (hAC : A ≤ C) (hCB : C ≤ B)
    (hdisplacements : ∀ g v, v ∈ B → rho g v - v ∈ C)
    (sigma : Representation k H X) (S : Submodule k[H] sigma.asModule)
    [FiniteDimensional k S] [IsSimpleModule k[H] S]
    (hnonfixed : ¬ representationSubmoduleFixed sigma S) :
    schurSocleMultiplicity (k := k) (R := k[H])
        (A := (inflatedRepresentation gamma (nestedQuotientRepresentation A B (hAC.trans hCB))).asModule)
        (X := S) ≤
      schurSocleMultiplicity (k := k) (R := k[H])
        (A := (inflatedRepresentation gamma (nestedQuotientRepresentation A C hAC)).asModule)
        (X := S) := by
  let tau := inflatedRepresentation gamma (nestedQuotientRepresentation A B (hAC.trans hCB))
  let nu := inflatedRepresentation gamma (nestedQuotientRepresentation A C hAC)
  let i : nu.IntertwiningMap tau :=
    { toLinearMap := (nestedQuotientInclusion A C B hAC hCB).toLinearMap
      isIntertwining' := fun g ↦
        (nestedQuotientInclusion A C B hAC hCB).isIntertwining' (gamma g) }
  apply schurSocleMultiplicity_le_of_nonfixed_displacements
    sigma S hnonfixed tau nu i (nestedQuotientInclusion_injective A C B hAC hCB)
  apply Submodule.span_le.mpr
  rintro _ ⟨⟨g, z⟩, rfl⟩
  obtain ⟨v, rfl⟩ := (nestedSubrepresentation A B (hAC.trans hCB)).toSubmodule.mkQ_surjective z
  let c : C.toSubmodule := ⟨rho (gamma g) v.1 - v.1,
    hdisplacements (gamma g) v.1 v.2⟩
  refine ⟨Submodule.Quotient.mk c, ?_⟩
  change (nestedSubrepresentation A B (hAC.trans hCB)).toSubmodule.mkQ
      (B.toRepresentation (gamma g) v - v) =
    (nestedSubrepresentation A B (hAC.trans hCB)).toSubmodule.mkQ
      (B.toRepresentation (gamma g) v) -
    (nestedSubrepresentation A B (hAC.trans hCB)).toSubmodule.mkQ v
  exact map_sub _ _ _

end SymmetricSubgroupAsymptotics

end
