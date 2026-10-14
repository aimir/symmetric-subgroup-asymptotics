import SymmetricSubgroupAsymptotics.SchurMultiplicity
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# A uniform target-Hom bound passes to actual quotient sections

The selected isotypic component of the actual quotient is pulled back to
an actual submodule of the original ambient module. Its maps to the same
simple type inject into maps from that original preimage. The component's
Hom dimension is its multiplicity times its actual Schur-ring dimension.
No duality, splitting of the source, or census hypothesis is required.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical BigOperators

namespace SymmetricSubgroupAsymptotics

variable {k R A X V : Type} [Field k] [Ring R] [Algebra k R]
  [AddCommGroup A] [Module R A] [Module k A] [IsScalarTower k R A]
  [AddCommGroup X] [Module R X] [Module k X] [IsScalarTower k R X]
  [AddCommGroup V] [Module R V] [Module k V] [IsScalarTower k R V]

/-- Maps out of the actual selected isotypic component have the same
dimension as maps into it from its defining simple type. -/
theorem schurIsotypic_targetHom_finrank
    [FiniteDimensional k A] [FiniteDimensional k X] [IsSimpleModule R X] :
    Module.finrank k (isotypicComponent R A X →ₗ[R] X) =
      schurSocleMultiplicity (k := k) (R := R) (A := A) (X := X) *
        Module.finrank k (Module.End R X) := by
  let n := schurSocleMultiplicity (k := k) (R := R) (A := A) (X := X)
  let e := schurSocleDecomposition (k := k) (R := R) (A := A) (X := X)
  calc
    _ = Module.finrank k ((Fin n → X) →ₗ[R] X) :=
      (schurHomCongrSource (k := k) (A := X) e).finrank_eq
    _ = Module.finrank k (Fin n → Module.End R X) :=
      (LinearMap.lsum R (fun _ : Fin n ↦ X) k).symm.finrank_eq
    _ = _ := by simp [Module.finrank_pi_fintype, n]

/-- A uniform bound on maps from original submodules to one simple
target bounds its multiplicity in every displayed original section. -/
theorem schurSocleMultiplicity_mul_end_le_of_section_uniform_targetHom
    [FiniteDimensional k A] [FiniteDimensional k X] [FiniteDimensional k V]
    [IsSimpleModule R X]
    (cap : ℕ)
    (hHom : ∀ N : Submodule R V, Module.finrank k (N →ₗ[R] X) ≤ cap)
    (M : Submodule R V) (q : M →ₗ[R] A) (hq : Function.Surjective q) :
    schurSocleMultiplicity (k := k) (R := R) (A := A) (X := X) *
      Module.finrank k (Module.End R X) ≤ cap := by
  let I := isotypicComponent R A X
  let N : Submodule R M := I.comap q
  let N' : Submodule R V := N.map M.subtype
  let e : N ≃ₗ[R] N' := M.equivSubtypeMap N
  let qN : N →ₗ[R] I :=
    (q.comp N.subtype).codRestrict I (fun v ↦ v.property)
  have hqN : Function.Surjective qN := by
    intro w
    obtain ⟨v, hv⟩ := hq w.val
    have hvN : v ∈ N := by
      change q v ∈ I
      rw [hv]
      exact w.property
    exact ⟨⟨v, hvN⟩, Subtype.ext hv⟩
  let qN' : N' →ₗ[R] I := qN.comp e.symm.toLinearMap
  have hqN' : Function.Surjective qN' := hqN.comp e.symm.surjective
  let precompose : (I →ₗ[R] X) →ₗ[k] (N' →ₗ[R] X) :=
    { toFun := fun f ↦ f.comp qN'
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  have hi : Function.Injective precompose := by
    intro f g h
    apply LinearMap.ext
    intro x
    obtain ⟨v, hv⟩ := hqN' x
    rw [← hv]
    exact LinearMap.congr_fun h v
  letI : FiniteDimensional k N' := FiniteDimensional.of_injective
    (N'.subtype.restrictScalars k) N'.subtype_injective
  have hdim := precompose.finrank_le_finrank_of_injective hi
  rw [schurIsotypic_targetHom_finrank (k := k) (R := R) (A := A) (X := X)] at hdim
  exact hdim.trans (hHom N')

end SymmetricSubgroupAsymptotics

end
