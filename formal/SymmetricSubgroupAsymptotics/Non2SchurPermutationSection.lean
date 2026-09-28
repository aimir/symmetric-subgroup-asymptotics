import SymmetricSubgroupAsymptotics.Non2SchurMixedSocleDimension
import SymmetricSubgroupAsymptotics.PermutationOrbitHeadSection

/-!
# Pulling the mixed Schur carrier through a permutation section

For an actual quotient of a permutation subrepresentation, pull the literal
mixed invariant/isotypic carrier back to its original preimage.  The selected
simple row kernel fixes that carrier pointwise.  The arbitrary orbit
filtration can therefore apply directly to the correct joint object, with no
embedding of the quotient back into the permutation module.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped BigOperators Classical MonoidAlgebra
attribute [local instance] Fintype.ofFinite

namespace SymmetricSubgroupAsymptotics

variable {B X A : Type} [Group B] [Finite B] [Finite X] [MulAction B X]
    [AddCommGroup A] [Module (ZMod 2) A] [FiniteDimensional (ZMod 2) A]

/-- A weighted local head bound on every literal orbit of the actual simple
row kernel bounds the literal mixed carrier of an original permutation
section. -/
theorem permutationSection_schurMixedSocle_finrank_weighted_le
    (sigma : Representation (ZMod 2) B A)
    (S : Submodule (ZMod 2)[B] sigma.asModule)
    [IsSimpleModule (ZMod 2)[B] S]
    (M : Subrepresentation
      (permutationFunctionRepresentation (ZMod 2) B X))
    (q : M.toRepresentation.IntertwiningMap sigma)
    (hq : Function.Surjective q)
    (a b : ℕ)
    (cap : MulAction.orbitRel.Quotient
      (schurSimpleActionKernel sigma S) X → ℕ)
    (hcap : ∀ (o : MulAction.orbitRel.Quotient
        (schurSimpleActionKernel sigma S) X)
      (T : Subrepresentation (permutationFunctionRepresentation (ZMod 2)
        (schurSimpleActionKernel sigma S) o.orbit)),
      Module.finrank (ZMod 2) (T.toRepresentation.IntertwiningMap
        (Representation.trivial (ZMod 2)
          (schurSimpleActionKernel sigma S) (ZMod 2))) ≤ cap o)
    (hweight : ∀ o : MulAction.orbitRel.Quotient
      (schurSimpleActionKernel sigma S) X,
      b * cap o ≤ a * Nat.card o.orbit) :
    b * Module.finrank (ZMod 2) (schurMixedSocleSubspace sigma S) ≤
      a * Nat.card X := by
  let K := schurSimpleActionKernel sigma S
  let W := schurMixedSocleSubspace sigma S
  let P : Submodule (ZMod 2) M.toSubmodule := W.comap q.toLinearMap
  let M' : Subrepresentation
      (permutationFunctionRepresentation (ZMod 2) K X) := {
    toSubmodule := P.map M.toSubmodule.subtype
    apply_mem_toSubmodule := by
      intro g v hv
      obtain ⟨v, hv, rfl⟩ := hv
      refine ⟨M.toRepresentation (g : B) v, ?_, rfl⟩
      change q (M.toRepresentation (g : B) v) ∈ W
      rw [Representation.IntertwiningMap.isIntertwining]
      have hfix := schurSimpleActionKernel_fixes_mixedSocle
        sigma S g ⟨q v, hv⟩
      have hfix' : sigma (g : B) (q v) = q v := by
        simpa only [Representation.single_smul, one_smul] using hfix
      rw [hfix']
      exact hv }
  let e : P ≃ₗ[ZMod 2] M'.toSubmodule :=
    M.toSubmodule.equivSubtypeMap P
  let qP : P →ₗ[ZMod 2] W :=
    (q.toLinearMap.comp P.subtype).codRestrict W (fun v => v.property)
  have hqP : Function.Surjective qP := by
    intro w
    obtain ⟨v, hv⟩ := hq (sigma.asModuleEquiv (w : sigma.asModule))
    have hvP : v ∈ P := by
      change sigma.asModuleEquiv.symm (q v) ∈ W
      rw [hv]
      simp only [LinearEquiv.symm_apply_apply]
      exact w.property
    refine ⟨⟨v, hvP⟩, Subtype.ext ?_⟩
    change sigma.asModuleEquiv.symm (q v) = w
    rw [hv, LinearEquiv.symm_apply_apply]
  let qM : M'.toSubmodule →ₗ[ZMod 2] W :=
    qP.comp e.symm.toLinearMap
  have hqM : Function.Surjective qM := hqP.comp e.symm.surjective
  have htrivial : ∀ (g : K) (m : M'.toSubmodule),
      qM (M'.toRepresentation g m) = qM m := by
    intro g m
    apply Subtype.ext
    change q (e.symm (M'.toRepresentation g m) : M.toSubmodule) =
      q (e.symm m : M.toSubmodule)
    have he : (e.symm (M'.toRepresentation g m) : M.toSubmodule) =
        M.toRepresentation (g : B) (e.symm m : M.toSubmodule) := by
      apply Subtype.ext
      rfl
    rw [he, Representation.IntertwiningMap.isIntertwining]
    have hfix := schurSimpleActionKernel_fixes_mixedSocle sigma S g
      ⟨q (e.symm m : M.toSubmodule), (e.symm m).property⟩
    simpa only [Representation.single_smul, one_smul] using hfix
  exact permutation_trivial_quotient_weighted_finrank_le
    a b cap hcap hweight M' qM hqM htrivial

/-- Numerical row form of the same result, after identifying the invariant
dimension parameter in `t + h*m`. -/
theorem permutationSection_schurMixedSocleDimension_weighted_le
    (sigma : Representation (ZMod 2) B A)
    (S : Submodule (ZMod 2)[B] sigma.asModule)
    [IsSimpleModule (ZMod 2)[B] S]
    (hnonfixed : ¬ representationSubmoduleFixed sigma S)
    (M : Subrepresentation
      (permutationFunctionRepresentation (ZMod 2) B X))
    (q : M.toRepresentation.IntertwiningMap sigma)
    (hq : Function.Surjective q)
    (t : ℕ) (ht : t = Module.finrank (ZMod 2) sigma.invariants)
    (a b : ℕ)
    (cap : MulAction.orbitRel.Quotient
      (schurSimpleActionKernel sigma S) X → ℕ)
    (hcap : ∀ (o : MulAction.orbitRel.Quotient
        (schurSimpleActionKernel sigma S) X)
      (T : Subrepresentation (permutationFunctionRepresentation (ZMod 2)
        (schurSimpleActionKernel sigma S) o.orbit)),
      Module.finrank (ZMod 2) (T.toRepresentation.IntertwiningMap
        (Representation.trivial (ZMod 2)
          (schurSimpleActionKernel sigma S) (ZMod 2))) ≤ cap o)
    (hweight : ∀ o : MulAction.orbitRel.Quotient
      (schurSimpleActionKernel sigma S) X,
      b * cap o ≤ a * Nat.card o.orbit) :
    b * schurMixedSocleDimension sigma S t ≤ a * Nat.card X := by
  subst t
  rw [← schurMixedSocleSubspace_finrank_eq sigma S hnonfixed]
  exact permutationSection_schurMixedSocle_finrank_weighted_le
    sigma S M q hq a b cap hcap hweight

end SymmetricSubgroupAsymptotics

end
