import SymmetricSubgroupAsymptotics.PermutationPGroupSection
import SymmetricSubgroupAsymptotics.SchurPGroupCapacity

/-!
# Schur capacity detected on a semiregular prime subgroup

The six-block ternary translation row needs a capacity of two rather than
the generic half-dimension capacity of three.  The saving is intrinsic to
the actual block action.  A Sylow-three subgroup has a fixed-point-free
element with two cyclic orbits.  The invariant space of every quotient of
an actual permutation subrepresentation is therefore at most two.

This file isolates the two general algebraic passages used by that argument.
First, a specified element bounds invariant quotients by its literal cyclic
orbit count.  Second, the Schur capacity of a representation of a finite
group is bounded by its invariant space on any defining-characteristic
finite p-subgroup.  The latter uses a nonzero fixed vector in each original
simple source; evaluation at that vector is injective because a nonzero map
from a simple module is injective.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical MonoidAlgebra

namespace SymmetricSubgroupAsymptotics

variable {k G I W A : Type} [Field k] [Group G] [MulAction G I]
  [Finite I] [AddCommGroup W] [Module k W]

/-- Every trivial quotient of an actual permutation subrepresentation is
bounded by the number of cyclic orbits of any specified original element.
No transitivity or p-group hypothesis is used. -/
theorem permutation_trivial_quotient_finrank_le_cyclicOrbitCount
    (M : Subrepresentation (permutationFunctionRepresentation k G I))
    (q : M.toSubmodule →ₗ[k] W) (hq : Function.Surjective q)
    (htrivial : ∀ (a : G) (m : M.toSubmodule),
      q (M.toRepresentation a m) = q m)
    (g : G) :
    Module.finrank k W ≤
      Nat.card (MulAction.orbitRel.Quotient (Subgroup.zpowers g) I) := by
  classical
  have hinvariant : ∀ a : G, q.comp (M.toRepresentation a) = q := by
    intro a
    apply LinearMap.ext
    exact htrivial a
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
  exact hdim.trans
    (permutation_subrepresentationHead_le_cyclicOrbitCount M g)

variable [AddCommGroup A] [Module k A]

/-- The invariant space of an equivariant quotient of an actual permutation
subrepresentation is controlled by the literal cyclic orbit count of any
specified acting element. -/
theorem permutationSection_invariants_finrank_le_cyclicOrbitCount
    (rho : Representation k G A)
    (M : Subrepresentation (permutationFunctionRepresentation k G I))
    (q : M.toRepresentation.IntertwiningMap rho)
    (hq : Function.Surjective q) (g : G) :
    Module.finrank k rho.invariants ≤
      Nat.card (MulAction.orbitRel.Quotient (Subgroup.zpowers g) I) := by
  let S := rho.invariants
  let P : Submodule k M.toSubmodule := S.comap q.toLinearMap
  have hfixed (a : G) (v : M.toSubmodule) (hv : v ∈ P) :
      q (M.toRepresentation a v) = q v := by
    rw [Representation.IntertwiningMap.isIntertwining]
    exact hv a
  let M' : Subrepresentation (permutationFunctionRepresentation k G I) := {
    toSubmodule := P.map M.toSubmodule.subtype
    apply_mem_toSubmodule := by
      intro a v hv
      obtain ⟨v, hv, rfl⟩ := hv
      refine ⟨M.toRepresentation a v, ?_, rfl⟩
      change q (M.toRepresentation a v) ∈ S
      rw [hfixed a v hv]
      exact hv }
  let e : P ≃ₗ[k] M'.toSubmodule := M.toSubmodule.equivSubtypeMap P
  let qP : P →ₗ[k] S :=
    (q.toLinearMap.comp P.subtype).codRestrict S (fun v ↦ v.property)
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
  have htrivial : ∀ (a : G) (m : M'.toSubmodule),
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
  exact permutation_trivial_quotient_finrank_le_cyclicOrbitCount
    M' qM hqM htrivial g

variable {p : ℕ} [Fact p.Prime]
variable {G₀ V : Type} [Group G₀] [Finite G₀]
  [AddCommGroup V] [Module (ZMod p) V] [Finite V]

omit [Finite G₀] in
/-- Restriction to a finite p-subgroup bounds the original Schur capacity
by the dimension of the subgroup-fixed space.  The simple modules and Hom
spaces remain those of the original group algebra. -/
theorem representationSchurCapacity_le_pSubgroup_invariants
    (P : Subgroup G₀) (hP : IsPGroup p P)
    (sigma : Representation (ZMod p) G₀ V) :
    representationSchurCapacity sigma ≤
      Module.finrank (ZMod p)
        (Representation.invariants (sigma.comp P.subtype)) := by
  unfold representationSchurCapacity schurCapacity
  apply csSup_le (Set.insert_nonempty _ _)
  rintro x (rfl | ⟨S, hS, rfl⟩)
  · exact_mod_cast (Nat.zero_le
      (Module.finrank (ZMod p)
        (Representation.invariants (sigma.comp P.subtype))))
  · letI := hS
    letI : FiniteDimensional (ZMod p) S := FiniteDimensional.of_injective
      (S.subtype.restrictScalars (ZMod p)) S.subtype_injective
    haveI : Nontrivial S := IsSimpleModule.nontrivial (ZMod p)[G₀] S
    let tau : Representation (ZMod p) P S :=
      (Subrepresentation.ofSubmodule' S).toRepresentation.comp P.subtype
    letI : Finite S := Module.finite_of_finite (ZMod p)
    obtain ⟨s, hs0, hsfixed⟩ := pGroup_representation_nonzero_fixed hP tau
    let ev : (S →ₗ[(ZMod p)[G₀]] sigma.asModule) →ₗ[ZMod p]
        (Representation.invariants (sigma.comp P.subtype)) := {
      toFun := fun f ↦ ⟨sigma.asModuleEquiv (f s), by
        intro a
        have hf := f.map_smul
          (MonoidAlgebra.single (a : G₀) (1 : ZMod p)) s
        have hs : MonoidAlgebra.single (a : G₀) (1 : ZMod p) • s = s := by
          apply Subtype.ext
          change MonoidAlgebra.single (a : G₀) (1 : ZMod p) •
              (s.1 : sigma.asModule) = (s.1 : sigma.asModule)
          rw [Representation.single_smul, one_smul]
          exact congrArg Subtype.val (hsfixed a)
        calc
          sigma a (sigma.asModuleEquiv (f s)) =
              sigma.asModuleEquiv
                (MonoidAlgebra.single (a : G₀) (1 : ZMod p) • f s) := by
            rw [Representation.asModuleEquiv_map_smul,
              Representation.asAlgebraHom_single, one_smul]
          _ = sigma.asModuleEquiv
                (f (MonoidAlgebra.single (a : G₀) (1 : ZMod p) • s)) := by
            rw [hf]
          _ = sigma.asModuleEquiv (f s) := by rw [hs]⟩
      map_add' := by intro f g; apply Subtype.ext; rfl
      map_smul' := by intro c f; apply Subtype.ext; rfl }
    have hev : Function.Injective ev := by
      intro f g hfg
      by_contra hne
      have hd : f - g ≠ 0 := sub_ne_zero.mpr hne
      have hinj : Function.Injective (f - g) :=
        LinearMap.injective_of_ne_zero hd
      have hzero : (f - g) s = 0 := by
        have hval := congrArg Subtype.val hfg
        have hfgs : f s = g s := sigma.asModuleEquiv.injective hval
        simpa only [LinearMap.sub_apply, sub_eq_zero] using hfgs
      exact hs0 (hinj (hzero.trans (map_zero (f - g)).symm))
    have hdim := ev.finrank_le_finrank_of_injective hev
    have hdimR :
        (Module.finrank (ZMod p)
          (S →ₗ[(ZMod p)[G₀]] sigma.asModule) : ℝ) ≤
          Module.finrank (ZMod p)
            (Representation.invariants (sigma.comp P.subtype)) := by
      exact_mod_cast hdim
    have hSone : (1 : ℝ) ≤ Module.finrank (ZMod p) S := by
      exact_mod_cast (Module.finrank_pos (R := ZMod p) (M := S))
    have hHomNonneg : (0 : ℝ) ≤ Module.finrank (ZMod p)
        (S →ₗ[(ZMod p)[G₀]] sigma.asModule) := by positivity
    exact (div_le_self hHomNonneg hSone).trans hdimR

end SymmetricSubgroupAsymptotics

end
