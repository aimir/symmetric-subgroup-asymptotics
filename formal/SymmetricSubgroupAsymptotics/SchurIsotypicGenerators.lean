import SymmetricSubgroupAsymptotics.TraceyPrimePowerInput
import Mathlib.RingTheory.SimpleModule.Basic
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.Data.Fintype.EquivFin

/-!
# Generators of one finite isotypic module

For a simple left `R`-module `X`, put `D = End_R(X)` and let `e` be the
dimension of `X` over `D`.  The Jacobson density theorem says that one
element of `R` can prescribe an arbitrary `D`-linear endomorphism of `X`.
Consequently `t` vectors generate `X^m` whenever `m ≤ t e`: pack the `m`
coordinates into `t` rows of an `e`-element `D`-basis and use density on
each row.

This is the algebraic packing statement used by the fixed-frame socle
argument.  It is independent of the particular permutation frame and does
not assume that the Schur division ring is the ground field.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics

universe u

/-- A module-theoretic version of `RepresentationGeneratedBy`. -/
def ModuleGeneratedBy
    (R M : Type u) [Semiring R] [AddCommMonoid M] [Module R M]
    (t : ℕ) : Prop :=
  ∃ v : Fin t → M, Submodule.span R (Set.range v) = ⊤

namespace ModuleGeneratedBy

variable {R M N : Type u} [Semiring R]
  [AddCommMonoid M] [Module R M]
  [AddCommMonoid N] [Module R N]

/-- Module generation is invariant under an `R`-linear equivalence. -/
theorem congr (e : M ≃ₗ[R] N) {t : ℕ} :
    ModuleGeneratedBy R M t → ModuleGeneratedBy R N t := by
  rintro ⟨v, hv⟩
  refine ⟨fun i ↦ e (v i), ?_⟩
  have hmap := congrArg (Submodule.map e.toLinearMap) hv
  rw [Submodule.map_top, LinearMap.range_eq_top.mpr e.surjective,
    Submodule.map_span] at hmap
  rw [← Set.range_comp] at hmap
  simpa only [Function.comp_apply] using hmap

end ModuleGeneratedBy

section OneIsotypicRow

variable {R X : Type u} [Ring R] [AddCommGroup X] [Module R X]
  [IsSimpleModule R X]

private abbrev SchurRing := Module.End R X

/-- The packed coordinate vectors attached to an embedding
`Fin m ↪ Fin t × Fin e`. -/
private def schurPackedVector
    {m t e : ℕ}
    (b : Module.Basis (Fin e) (SchurRing (R := R) (X := X)) X)
    (j : Fin m ↪ Fin t × Fin e) (a : Fin t) : Fin m → X :=
  fun i ↦ if (j i).1 = a then b (j i).2 else 0

/-- On the coordinates assigned to one packed row, prescribe the desired
output; injectivity of the packing makes this unambiguous. -/
private def schurPackedTarget
    {m t e : ℕ} (j : Fin m ↪ Fin t × Fin e)
    (y : Fin m → X) (a : Fin t) (r : Fin e) : X :=
  if h : ∃ i : Fin m, j i = (a, r) then y (Classical.choose h) else 0

private theorem schurPackedTarget_apply
    {m t e : ℕ} (j : Fin m ↪ Fin t × Fin e)
    (y : Fin m → X) (i : Fin m) :
    schurPackedTarget j y (j i).1 (j i).2 = y i := by
  unfold schurPackedTarget
  split_ifs with h
  · exact congrArg y (j.injective (Classical.choose_spec h))
  · exact (h ⟨i, Prod.ext rfl rfl⟩).elim

/-- Jacobson-density packing for one isotypic row.  The basis is explicit
so later consumers may retain the actual Schur dimension rather than
silently replace it by the ground-field dimension. -/
theorem schurPi_moduleGeneratedBy_of_multiplicity_le
    (m t e : ℕ)
    (b : Module.Basis (Fin e) (SchurRing (R := R) (X := X)) X)
    (hm : m ≤ t * e) :
    ModuleGeneratedBy R (Fin m → X) t := by
  classical
  letI : Module.Finite (SchurRing (R := R) (X := X)) X :=
    Module.Finite.of_basis b
  let j : Fin m ↪ Fin t × Fin e :=
    Classical.choice (Function.Embedding.nonempty_of_card_le (by
      simpa only [Fintype.card_fin, Fintype.card_prod] using hm))
  let v : Fin t → (Fin m → X) :=
    fun a ↦ schurPackedVector b j a
  refine ⟨v, top_unique ?_⟩
  intro y _hy
  let f : Fin t → Module.End (SchurRing (R := R) (X := X)) X :=
    fun a ↦ b.constr ℕ
      (schurPackedTarget j y a)
  have hsurj : Function.Surjective
      (Module.toModuleEnd (SchurRing (R := R) (X := X))
        (S := R) X) :=
    Module.Finite.toModuleEnd_moduleEnd_surjective
  choose r hr using fun a : Fin t ↦ hsurj (f a)
  have hsum : y = ∑ a : Fin t, r a • v a := by
    funext i
    rw [Finset.sum_apply, Finset.sum_eq_single (j i).1]
    · change y i = r (j i).1 • schurPackedVector b j (j i).1 i
      rw [schurPackedVector, if_pos rfl]
      have happ := LinearMap.congr_fun (hr (j i).1) (b (j i).2)
      change r (j i).1 • b (j i).2 =
        f (j i).1 (b (j i).2) at happ
      rw [show f (j i).1 (b (j i).2) =
          schurPackedTarget j y (j i).1 (j i).2 by
        dsimp only [f]
        exact Module.Basis.constr_basis b ℕ _ _] at happ
      exact (happ.trans (schurPackedTarget_apply j y i)).symm
    · intro a _ha hane
      change r a • schurPackedVector b j a i = 0
      rw [schurPackedVector, if_neg (Ne.symm hane), smul_zero]
    · intro hnot
      exact (hnot (Finset.mem_univ _)).elim
  rw [hsum]
  apply Submodule.sum_mem
  intro a _ha
  apply Submodule.smul_mem
  exact Submodule.subset_span (Set.mem_range_self a)

/-- Canonical numerical specialization using the finite Schur basis. -/
theorem schurPi_moduleGeneratedBy
    [Module.Finite (SchurRing (R := R) (X := X)) X]
    (m t : ℕ)
    (hm : m ≤ t * Module.finrank (SchurRing (R := R) (X := X)) X) :
    ModuleGeneratedBy R (Fin m → X) t :=
  schurPi_moduleGeneratedBy_of_multiplicity_le m t _
    (Module.finBasis (SchurRing (R := R) (X := X)) X) hm

end OneIsotypicRow

end SymmetricSubgroupAsymptotics

end
