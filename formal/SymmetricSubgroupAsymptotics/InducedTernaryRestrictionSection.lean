import SymmetricSubgroupAsymptotics.InducedTernaryWidthEnvelope
import SymmetricSubgroupAsymptotics.TernaryIndexWidthValues
import Mathlib.RepresentationTheory.Invariants

/-!
# Quotient sections of a Sylow-restricted induced module

The ordinary ternary induced-head theorem starts with a subrepresentation
for the whole group and then restricts it to a Sylow subgroup.  A normal
section of the affine kernel has the opposite shape: after restricting the
ambient induced module, take an arbitrary Sylow-stable preimage and quotient
it onto the section's invariant space.

The Mackey coordinate proof is unchanged.  This file states it directly for
an arbitrary subrepresentation of the restricted induced module and then
passes to invariant quotients.  At index six and one-dimensional local
fibre the canonical integer width is exactly two.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics

attribute [local instance]
  inducedMackeyComponentAddCommGroup inducedMackeyComponentModule

variable {k G V A : Type} [Field k] [Group G] [Finite G]
  [AddCommGroup V] [Module k V]
  [FiniteDimensional k V]

/-- Mackey projection of an arbitrary subrepresentation after restriction
to the actual Sylow subgroup. -/
def inducedMackeySylowRestrictedSubmoduleCoordinate
    (H : Subgroup G) (P : Sylow 3 G)
    (rho : Representation k H V)
    [Fintype (DoubleCoset.Quotient (H : Set G) ((P : Subgroup G) : Set G))]
    (M : Subrepresentation
      ((Representation.ind H.subtype rho).comp (P : Subgroup G).subtype))
    (q : DoubleCoset.Quotient (H : Set G) ((P : Subgroup G) : Set G)) :
    M.toRepresentation.IntertwiningMap
      (Representation.ind
        (inducedOrbitStabilizer H (P : Subgroup G) q.out).subtype
        (inducedOrbitFibre H (P : Subgroup G) rho q.out)) where
  toLinearMap := (LinearMap.proj q).comp
    ((inducedMackeyDecomposition H (P : Subgroup G) rho).toLinearMap.comp
      M.toSubmodule.subtype)
  isIntertwining' p := by
    apply LinearMap.ext
    intro v
    exact inducedMackeyDecomposition_equivariant
      H (P : Subgroup G) rho p v.1 q

omit [FiniteDimensional k V] in
theorem inducedMackeySylowRestrictedSubmoduleCoordinate_injective
    (H : Subgroup G) (P : Sylow 3 G)
    (rho : Representation k H V)
    [Fintype (DoubleCoset.Quotient (H : Set G) ((P : Subgroup G) : Set G))]
    (M : Subrepresentation
      ((Representation.ind H.subtype rho).comp (P : Subgroup G).subtype)) :
    Function.Injective (fun v q ↦
      inducedMackeySylowRestrictedSubmoduleCoordinate H P rho M q v) := by
  intro v w h
  apply Subtype.ext
  apply (inducedMackeyDecomposition H (P : Subgroup G) rho).injective
  exact h

/-- The integer ternary width bound applies to every subrepresentation of
the Sylow-restricted induced module, not only restrictions of original
whole-group subrepresentations. -/
theorem inducedRestrictionTernary_head_le_widthCore
    (H : Subgroup G) (rho : Representation k H V)
    (P : Sylow 3 G)
    (M : Subrepresentation
      ((Representation.ind H.subtype rho).comp (P : Subgroup G).subtype)) :
    Module.finrank k
      (M.toRepresentation.IntertwiningMap
        (Representation.trivial k P k)) ≤
      Module.finrank k V *
        ternaryWidthCore H.index (H.index.factorization 3) := by
  letI : Finite
      (DoubleCoset.Quotient (H : Set G) ((P : Subgroup G) : Set G)) :=
    Finite.of_injective
      (inducedDoubleCosetOrbitEquiv H (P : Subgroup G))
      (inducedDoubleCosetOrbitEquiv H (P : Subgroup G)).injective
  letI : Fintype
      (DoubleCoset.Quotient (H : Set G) ((P : Subgroup G) : Set G)) :=
    Fintype.ofFinite _
  obtain ⟨j, hj, hkj, hs⟩ := inducedMackeySylow_indices H 3 P
  have hlocal : Module.finrank k
      (M.toRepresentation.IntertwiningMap
        (Representation.trivial k P k)) ≤
      ∑ q, Module.finrank k V * ternaryLocalWidth (j q) := by
    apply representationHom_finrank_le_coordinates
      (fun q ↦ inducedMackeyComponent H (P : Subgroup G) rho q)
      M.toRepresentation
      (fun q ↦ Representation.ind
        (inducedOrbitStabilizer H (P : Subgroup G) q.out).subtype
        (inducedOrbitFibre H (P : Subgroup G) rho q.out))
      (Representation.trivial k P k)
      (fun q ↦ Module.finrank k V * ternaryLocalWidth (j q))
      (fun q S ↦ threeGroup_induced_subrepresentationHead_le
        P.isPGroup'
        (inducedOrbitStabilizer H (P : Subgroup G) q.out)
        (inducedOrbitFibre H (P : Subgroup G) rho q.out)
        (j q) (hj q) S)
      (inducedMackeySylowRestrictedSubmoduleCoordinate H P rho M)
      (inducedMackeySylowRestrictedSubmoduleCoordinate_injective H P rho M)
  exact hlocal.trans
    (ternaryLocalWidth_weighted_sum_le_core
      (Module.finrank k V) j H.index
      (H.index.factorization 3) hkj hs)

set_option maxHeartbeats 800000 in
/-- An invariant quotient of an arbitrary subrepresentation of the
Sylow-restricted induced module has the same integer width bound. -/
theorem inducedRestrictionTernary_section_invariants_le_widthCore
    (H : Subgroup G) (rho : Representation k H V)
    (P : Sylow 3 G)
    [AddCommGroup A] [Module k A]
    (M : Subrepresentation
      ((Representation.ind H.subtype rho).comp (P : Subgroup G).subtype))
    (sigma : Representation k P A)
    (q : M.toRepresentation.IntertwiningMap sigma)
    (hq : Function.Surjective q) :
    Module.finrank k sigma.invariants ≤
      Module.finrank k V *
        ternaryWidthCore H.index (H.index.factorization 3) := by
  let S := sigma.invariants
  let K : Submodule k M.toSubmodule := S.comap q.toLinearMap
  have hfixed (a : P) (v : M.toSubmodule) (hv : v ∈ K) :
      q (M.toRepresentation a v) = q v := by
    rw [Representation.IntertwiningMap.isIntertwining]
    exact hv a
  let M' : Subrepresentation
      ((Representation.ind H.subtype rho).comp (P : Subgroup G).subtype) := {
    toSubmodule := K.map M.toSubmodule.subtype
    apply_mem_toSubmodule := by
      intro a v hv
      obtain ⟨v, hv, rfl⟩ := hv
      refine ⟨M.toRepresentation a v, ?_, rfl⟩
      change q (M.toRepresentation a v) ∈ S
      rw [hfixed a v hv]
      exact hv }
  let e : K ≃ₗ[k] M'.toSubmodule :=
    M.toSubmodule.equivSubtypeMap K
  let qK : K →ₗ[k] S :=
    (q.toLinearMap.comp K.subtype).codRestrict S (fun v ↦ v.property)
  have hqK : Function.Surjective qK := by
    intro s
    obtain ⟨v, hv⟩ := hq (s : A)
    have hvK : v ∈ K := by
      change q v ∈ S
      rw [hv]
      exact s.property
    exact ⟨⟨v, hvK⟩, Subtype.ext hv⟩
  let qM : M'.toSubmodule →ₗ[k] S :=
    qK.comp e.symm.toLinearMap
  have hqM : Function.Surjective qM := hqK.comp e.symm.surjective
  have htrivial : ∀ (a : P) (m : M'.toSubmodule),
      qM (M'.toRepresentation a m) = qM m := by
    intro a m
    apply Subtype.ext
    change q (e.symm (M'.toRepresentation a m) : M.toSubmodule) =
      q (e.symm m : M.toSubmodule)
    have he : (e.symm (M'.toRepresentation a m) : M.toSubmodule) =
        M.toRepresentation a (e.symm m : M.toSubmodule) := by
      apply Subtype.ext
      rfl
    rw [he]
    exact hfixed a (e.symm m : M.toSubmodule) (e.symm m).property
  let q' : M'.toRepresentation.Coinvariants →ₗ[k] S :=
    Representation.Coinvariants.lift M'.toRepresentation qM (by
      intro a
      apply LinearMap.ext
      exact htrivial a)
  have hq' : Function.Surjective q' := by
    intro s
    obtain ⟨m, hm⟩ := hqM s
    exact ⟨Representation.Coinvariants.mk M'.toRepresentation m, hm⟩
  have hdim : Module.finrank k S ≤
      Module.finrank k M'.toRepresentation.Coinvariants :=
    LinearMap.finrank_le_finrank_of_surjective hq'
  rw [← representationHead_finrank_eq_coinvariants] at hdim
  exact hdim.trans
    (inducedRestrictionTernary_head_le_widthCore H rho P M')

/-- The only numerical specialization needed by the regular local-C3
six-block affine cell. -/
theorem inducedRestrictionTernary_section_invariants_le_two_of_index_six
    (H : Subgroup G) (rho : Representation k H V)
    (P : Sylow 3 G)
    [AddCommGroup A] [Module k A]
    (M : Subrepresentation
      ((Representation.ind H.subtype rho).comp (P : Subgroup G).subtype))
    (sigma : Representation k P A)
    (q : M.toRepresentation.IntertwiningMap sigma)
    (hq : Function.Surjective q)
    (hindex : H.index = 6)
    (hdim : Module.finrank k V = 1) :
    Module.finrank k sigma.invariants ≤ 2 := by
  have h := inducedRestrictionTernary_section_invariants_le_widthCore
    H rho P M sigma q hq
  rw [hindex, hdim] at h
  have hf : (6 : ℕ).factorization 3 = 1 := by decide +kernel
  norm_num [ternaryWidthCore, hf] at h
  exact h

end SymmetricSubgroupAsymptotics

end
