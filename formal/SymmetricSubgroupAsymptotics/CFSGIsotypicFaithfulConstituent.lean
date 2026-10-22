import SymmetricSubgroupAsymptotics.CliffordRestriction
import Mathlib.LinearAlgebra.Pi

/-! A faithful isotypic normal restriction is an actual repetition of a
faithful irreducible constituent. The coordinate equivalence is linear on
the original carrier and intertwines every original subgroup element. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical MonoidAlgebra

namespace SymmetricSubgroupAsymptotics.CFSGIsotypicFaithfulConstituent

variable {k G V : Type} [Field k] [Group G] [Finite G]
  [AddCommGroup V] [Module k V] [Finite V] [FiniteDimensional k V]

abbrev restriction (rho : Representation k G V) (H : Subgroup G) : Representation k H V :=
  rho.comp H.subtype

theorem exists_faithful_repeated_constituent
    (rho : Representation k G V) (hrho : Representation.IsIrreducible rho)
    (hf : Function.Injective rho) (H : Subgroup G) [H.Normal]
    (hiso : IsIsotypic k[H] (restriction rho H).asModule) :
    ∃ (n : ℕ) (S : Submodule k[H] (restriction rho H).asModule),
      0 < n ∧ IsSimpleModule k[H] S ∧
      ∃ e : V ≃ₗ[k] (Fin n → S),
        (∀ (h : H) (v : V) (i : Fin n), e (rho (h : G) v) i =
          Representation.ofModule (k := k) (G := H) S h (e v i)) ∧
        Function.Injective (Representation.ofModule (k := k) (G := H) S) := by
  let tau : Representation k H V := rho.comp H.subtype
  letI : Representation.IsIrreducible rho := hrho
  letI : Nontrivial V := Subrepresentation.irreducible_module_nontrivial rho
  letI : Nontrivial tau.asModule := tau.asModuleEquiv.toEquiv.nontrivial
  letI : Finite tau.asModule := Finite.of_injective
    tau.asModuleEquiv tau.asModuleEquiv.injective
  letI : Module.Finite k[H] tau.asModule := Module.Finite.of_finite
  letI : IsSemisimpleModule k[H] tau.asModule :=
    CliffordRawRestriction.proved.semisimple rho hrho H
  obtain ⟨n, hn, S, hs, ⟨f⟩⟩ := hiso.linearEquiv_fun
  let e : V ≃ₗ[k] (Fin n → S) := tau.asModuleEquiv.symm.trans (f.restrictScalars k)
  have he (h : H) (v : V) (i : Fin n) :
      e (rho (h : G) v) i = Representation.ofModule (k := k) (G := H) S h (e v i) := by
    change f (tau.asModuleEquiv.symm (tau h v)) i =
      Representation.ofModule (k := k) (G := H) S h (f (tau.asModuleEquiv.symm v) i)
    rw [Representation.asModuleEquiv_symm_map_rho, map_smul]
    rfl
  refine ⟨n, S, Nat.pos_of_ne_zero hn.out, hs, e, he, ?_⟩
  intro a b hab
  apply Subtype.ext
  apply hf
  apply LinearMap.ext
  intro v
  apply e.injective
  funext i
  rw [he, he]
  exact LinearMap.congr_fun hab (e v i)

end SymmetricSubgroupAsymptotics.CFSGIsotypicFaithfulConstituent
