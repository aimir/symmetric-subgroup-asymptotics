import SymmetricSubgroupAsymptotics.PermutationSubrepresentationHead
import SymmetricSubgroupAsymptotics.RepresentationCoinvariantHead
import Mathlib.RepresentationTheory.Coinvariants
import Mathlib.RepresentationTheory.Invariants

/-!
# Invariant quotients of permutation subrepresentations for p-groups

A trivial quotient of an actual permutation subrepresentation factors
through its intrinsic coinvariants.  Pulling the invariant space of an
arbitrary equivariant quotient back to the original permutation module
therefore gives the uniform `degree / p` bound supplied by a central
semiregular element.
-/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics

variable {p : ℕ} [Fact p.Prime]
variable {k G I W A : Type} [Field k] [Group G] [MulAction G I]
variable [Finite I] [Nontrivial I] [MulAction.IsPretransitive G I]
variable [AddCommGroup W] [Module k W]

/-- Every trivial quotient of an actual permutation subrepresentation has
dimension at most `degree / p`. -/
theorem pGroup_permutation_trivial_quotient_finrank_le_div
    (hG : IsPGroup p G)
    (M : Subrepresentation (permutationFunctionRepresentation k G I))
    (q : M.toSubmodule →ₗ[k] W) (hq : Function.Surjective q)
    (htrivial : ∀ (g : G) (m : M.toSubmodule),
      q (M.toRepresentation g m) = q m) :
    Module.finrank k W ≤ Nat.card I / p := by
  classical
  have hinvariant : ∀ g : G, q.comp (M.toRepresentation g) = q := by
    intro g
    apply LinearMap.ext
    exact htrivial g
  let q' : M.toRepresentation.Coinvariants →ₗ[k] W :=
    Representation.Coinvariants.lift M.toRepresentation q hinvariant
  have hq' : Function.Surjective q' := by
    intro w
    obtain ⟨m, hm⟩ := hq w
    exact ⟨Representation.Coinvariants.mk M.toRepresentation m, hm⟩
  have hdim : Module.finrank k W ≤
      Module.finrank k M.toRepresentation.Coinvariants :=
    LinearMap.finrank_le_finrank_of_surjective hq'
  rw [← representationHead_finrank_eq_coinvariants] at hdim
  exact hdim.trans (pGroup_permutationSubrepresentationHead_le_div hG M)

variable [AddCommGroup A] [Module k A]

/-- The whole invariant space of an equivariant permutation section is a
trivial quotient of its exact preimage in the original permutation module. -/
theorem pGroup_permutationSection_invariants_finrank_le_div
    (hG : IsPGroup p G) (ρ : Representation k G A)
    (M : Subrepresentation (permutationFunctionRepresentation k G I))
    (q : M.toRepresentation.IntertwiningMap ρ)
    (hq : Function.Surjective q) :
    Module.finrank k ρ.invariants ≤ Nat.card I / p := by
  let S := ρ.invariants
  let P : Submodule k M.toSubmodule := S.comap q.toLinearMap
  have hfixed (g : G) (v : M.toSubmodule) (hv : v ∈ P) :
      q (M.toRepresentation g v) = q v := by
    rw [Representation.IntertwiningMap.isIntertwining]
    exact hv g
  let M' : Subrepresentation (permutationFunctionRepresentation k G I) := {
    toSubmodule := P.map M.toSubmodule.subtype
    apply_mem_toSubmodule := by
      intro g v hv
      obtain ⟨v, hv, rfl⟩ := hv
      refine ⟨M.toRepresentation g v, ?_, rfl⟩
      change q (M.toRepresentation g v) ∈ S
      rw [hfixed g v hv]
      exact hv }
  let e : P ≃ₗ[k] M'.toSubmodule := M.toSubmodule.equivSubtypeMap P
  let qP : P →ₗ[k] S :=
    (q.toLinearMap.comp P.subtype).codRestrict S (fun v => v.property)
  have hqP : Function.Surjective qP := by
    intro s
    obtain ⟨v, hv⟩ := hq (s : A)
    have hvP : v ∈ P := by
      change q v ∈ S
      rw [hv]
      exact s.property
    exact ⟨⟨v, hvP⟩, Subtype.ext hv⟩
  let qM : M'.toSubmodule →ₗ[k] S := qP.comp e.symm.toLinearMap
  have hqM : Function.Surjective qM := hqP.comp e.symm.surjective
  have htrivial : ∀ (g : G) (m : M'.toSubmodule),
      qM (M'.toRepresentation g m) = qM m := by
    intro g m
    apply Subtype.ext
    change q (e.symm (M'.toRepresentation g m) : M.toSubmodule) =
      q (e.symm m : M.toSubmodule)
    have he : (e.symm (M'.toRepresentation g m) : M.toSubmodule) =
        M.toRepresentation g (e.symm m : M.toSubmodule) := by
      apply Subtype.ext
      rfl
    rw [he]
    exact hfixed g (e.symm m : M.toSubmodule) (e.symm m).property
  exact pGroup_permutation_trivial_quotient_finrank_le_div
    hG M' qM hqM htrivial

end SymmetricSubgroupAsymptotics

end
