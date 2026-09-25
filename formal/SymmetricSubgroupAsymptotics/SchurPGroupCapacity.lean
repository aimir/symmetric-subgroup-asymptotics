import SymmetricSubgroupAsymptotics.SchurRepresentation
import Mathlib.Algebra.Field.ZMod
import Mathlib.RepresentationTheory.Invariants
import Mathlib.GroupTheory.PGroup

/-! In defining characteristic, the simple constituents of a finite p-group
are trivial. The original representation's Schur capacity is therefore
computed by its actual fixed subspace, without replacing its action. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped MonoidAlgebra

namespace SymmetricSubgroupAsymptotics

universe u v
variable {p : ℕ} [Fact p.Prime]
variable {G : Type u} {V : Type v} [Group G] [AddCommGroup V] [Module (ZMod p) V]

theorem pGroup_representation_nonzero_fixed [Finite V] [Nontrivial V]
    (hG : IsPGroup p G) (ρ : Representation (ZMod p) G V) :
    ∃ v : V, v≠0 ∧ ∀ g, ρ g v=v := by
  letI : MulAction G V := {
    smul g v := ρ g v
    one_smul v := by change ρ 1 v=v; simp
    mul_smul g h v := by change ρ (g*h) v=ρ g (ρ h v); rw [map_mul]; rfl }
  have hcard : p ∣ Nat.card V := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod p), Nat.card_eq_fintype_card, ZMod.card]
    exact dvd_pow_self p (ne_of_gt (Module.finrank_pos (R := ZMod p) (M := V)))
  have hzero : (0:V)∈MulAction.fixedPoints G V := by
    intro g
    exact map_zero (ρ g)
  obtain ⟨v,hv,hv0⟩ := hG.exists_fixed_point_of_prime_dvd_card_of_fixed_point V hcard hzero
  exact ⟨v,Ne.symm hv0,hv⟩

/-- All vectors in a simple defining-characteristic representation are fixed. -/
theorem pGroup_simple_representation_trivial [Finite V]
    (hG : IsPGroup p G) (ρ : Representation (ZMod p) G V)
    [IsSimpleModule (ZMod p)[G] ρ.asModule] : ∀ g v, ρ g v=v := by
  haveI : Nontrivial ρ.asModule := IsSimpleModule.nontrivial (ZMod p)[G] ρ.asModule
  haveI : Nontrivial V := ρ.asModuleEquiv.toEquiv.symm.nontrivial
  obtain ⟨v,hv,hfixed⟩ := pGroup_representation_nonzero_fixed hG ρ
  let W : Subrepresentation ρ :=
    ⟨ρ.invariants, fun g x hx => by rw [hx g]; exact hx⟩
  have htop : W.asSubmodule=⊤ := by
    apply (eq_bot_or_eq_top W.asSubmodule).resolve_left
    intro hz
    have hx : (ρ.asModuleEquiv.symm v)∈W.asSubmodule := hfixed
    rw [hz] at hx
    have : ρ.asModuleEquiv.symm v=0 := hx
    exact hv (by simpa using congrArg ρ.asModuleEquiv this)
  intro g x
  have hx : ρ.asModuleEquiv.symm x∈W.asSubmodule := by rw [htop]; trivial
  exact hx g

/-- Evaluation at one identifies the actual invariant vectors. -/
def trivialScalarIntertwiningInvariants {k G A : Type*} [Field k] [Group G]
    [AddCommGroup A] [Module k A] (σ : Representation k G A) :
    (Representation.trivial k G k).IntertwiningMap σ ≃ₗ[k] σ.invariants where
  toFun f := ⟨f 1, fun g => by
    simpa using (Representation.IntertwiningMap.isIntertwining _ _ f g 1).symm⟩
  invFun a := (LinearMap.toSpanSingleton k A a.1).intertwiningMap_of_isIntertwiningMap
    _ _ (by
      intro g t
      change t • a.1=σ g (t • a.1)
      rw [map_smul,a.2 g])
  left_inv f := by
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro t
    change t • f 1=f t
    simpa using (f.toLinearMap.map_smul t (1:k)).symm
  right_inv a := by apply Subtype.ext; simp
  map_add' f g := by apply Subtype.ext; rfl
  map_smul' t f := by apply Subtype.ext; rfl

theorem pGroup_simple_module_fixed {M : Type*} [AddCommGroup M]
    [Module (ZMod p)[G] M] [Finite M] [IsSimpleModule (ZMod p)[G] M]
    (hG : IsPGroup p G) :
    ∀ (g : G) (x : M), MonoidAlgebra.single g (1:ZMod p) • x=x := by
  haveI : Nontrivial M := IsSimpleModule.nontrivial (ZMod p)[G] M
  let ρ := Representation.ofModule (k := ZMod p) (G := G) M
  letI : Finite (RestrictScalars (ZMod p) (ZMod p)[G] M) :=
    Finite.of_equiv M (RestrictScalars.addEquiv (ZMod p) (ZMod p)[G] M).symm.toEquiv
  letI : Nontrivial (RestrictScalars (ZMod p) (ZMod p)[G] M) :=
    (RestrictScalars.addEquiv (ZMod p) (ZMod p)[G] M).toEquiv.nontrivial
  obtain ⟨v,hv,hfixed⟩ := pGroup_representation_nonzero_fixed hG ρ
  let W : Subrepresentation ρ :=
    ⟨ρ.invariants, fun g x hx => by rw [hx g]; exact hx⟩
  have htop : W.asSubmodule'=⊤ := by
    apply (eq_bot_or_eq_top W.asSubmodule').resolve_left
    intro hz
    have hx : v∈W.asSubmodule' := hfixed
    rw [hz] at hx
    exact hv hx
  intro g x
  have hx : x∈W.asSubmodule' := by rw [htop]; trivial
  have h := hx g
  simpa [ρ,Representation.ofModule,RestrictScalars.lsmul] using h

section Capacity
variable {G₀ A : Type} [Group G₀] [AddCommGroup A] [Module (ZMod p) A]

/-- A simple source can map only into the original fixed subspace. -/
def pGroupSimpleHomToInvariants [Finite A]
    (hG : IsPGroup p G₀) (σ : Representation (ZMod p) G₀ A)
    (S : Submodule (ZMod p)[G₀] σ.asModule) [IsSimpleModule (ZMod p)[G₀] S] :
    (S →ₗ[(ZMod p)[G₀]] σ.asModule) →ₗ[ZMod p] (S →ₗ[ZMod p] σ.invariants) where
  toFun f := (σ.asModuleEquiv.toLinearMap.comp (f.restrictScalars (ZMod p))).codRestrict
    σ.invariants (fun x g => by
      letI : Finite σ.asModule := Finite.of_equiv A σ.asModuleEquiv.symm.toEquiv
      have h := f.map_smul (MonoidAlgebra.single g (1:ZMod p)) x
      rw [pGroup_simple_module_fixed hG] at h
      simpa only [Representation.single_smul,one_smul] using h.symm)
  map_add' f g := by ext x; rfl
  map_smul' t f := by ext x; rfl

theorem pGroupSimpleHomToInvariants_injective [Finite A]
    (hG : IsPGroup p G₀) (σ : Representation (ZMod p) G₀ A)
    (S : Submodule (ZMod p)[G₀] σ.asModule) [IsSimpleModule (ZMod p)[G₀] S] :
    Function.Injective (pGroupSimpleHomToInvariants hG σ S) := by
  intro f g h
  apply LinearMap.ext
  intro x
  apply σ.asModuleEquiv.injective
  exact congrArg Subtype.val (congrArg (fun F : S →ₗ[ZMod p] σ.invariants => F x) h)

/-- The Schur capacity of a finite p-group in characteristic p is exactly
the dimension of the original invariant subspace. No semisimplicity is used. -/
theorem pGroup_representationSchurCapacity [Finite A]
    (hG : IsPGroup p G₀) (σ : Representation (ZMod p) G₀ A) :
    representationSchurCapacity σ = (Module.finrank (ZMod p) σ.invariants:ℝ) := by
  apply le_antisymm
  · unfold representationSchurCapacity schurCapacity
    apply csSup_le (Set.insert_nonempty _ _)
    rintro x (rfl | ⟨S,hS,rfl⟩)
    · positivity
    · letI := hS
      letI : FiniteDimensional (ZMod p) S := FiniteDimensional.of_injective
        (S.subtype.restrictScalars (ZMod p)) S.subtype_injective
      haveI : Nontrivial S := IsSimpleModule.nontrivial (ZMod p)[G₀] S
      have hdim : 0<(Module.finrank (ZMod p) S:ℝ) := by
        exact_mod_cast (Module.finrank_pos (R := ZMod p) (M := S))
      have h := LinearMap.finrank_le_finrank_of_injective
        (pGroupSimpleHomToInvariants_injective hG σ S)
      rw [Module.finrank_linearMap (ZMod p) (ZMod p) S σ.invariants] at h
      apply (div_le_iff₀ hdim).mpr
      have hR : (Module.finrank (ZMod p) (S →ₗ[(ZMod p)[G₀]] σ.asModule):ℝ) ≤
          (Module.finrank (ZMod p) S:ℝ)*Module.finrank (ZMod p) σ.invariants := by
        exact_mod_cast h
      simpa only [mul_comm] using hR
  · have h := intertwiningMap_finrank_le_schur (Representation.trivial (ZMod p) G₀ (ZMod p)) σ
    rw [(trivialScalarIntertwiningInvariants σ).finrank_eq,
      Module.finrank_self,Nat.cast_one,mul_one] at h
    exact h

end Capacity

end SymmetricSubgroupAsymptotics
