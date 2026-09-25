import SymmetricSubgroupAsymptotics.ComplementCount

/-!
# Rank decomposition of actual weighted binary subspaces

The weight may depend on every retained part of a subspace. Grouping by rank
does not replace the subspace by its dimension or discard any incidence data.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics

attribute [local instance] Fintype.ofFinite

/-- Exact decomposition of an arbitrary weight on actual binary subspaces
by their finite ranks. -/
theorem binary_subspace_sum_by_rank {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [Finite V] (f : Submodule (ZMod 2) V → ℝ) :
    ∑ U, f U = ∑ k ∈ Finset.range (Module.finrank (ZMod 2) V + 1),
      ∑ U : {U : Submodule (ZMod 2) V // Module.finrank (ZMod 2) U = k}, f U.val := by
  classical
  let b : Submodule (ZMod 2) V → Fin (Module.finrank (ZMod 2) V + 1) :=
    fun U ↦ ⟨Module.finrank (ZMod 2) U,Nat.lt_succ_of_le U.finrank_le⟩
  calc
    _ = ∑ k : Fin (Module.finrank (ZMod 2) V + 1), ∑ U : {U // b U = k}, f U.val :=
      (Fintype.sum_fiberwise b f).symm
    _ = ∑ k : Fin (Module.finrank (ZMod 2) V + 1),
        ∑ U : {U : Submodule (ZMod 2) V // Module.finrank (ZMod 2) U = (k : ℕ)}, f U.val := by
      apply Finset.sum_congr rfl
      intro k hk
      let e : {U // b U = k} ≃
          {U : Submodule (ZMod 2) V // Module.finrank (ZMod 2) U = (k : ℕ)} :=
        Equiv.subtypeEquivRight fun U ↦ Fin.ext_iff
      exact Fintype.sum_equiv e _ _ (fun _ ↦ rfl)
    _ = _ := Fin.sum_univ_eq_sum_range
      (fun k : ℕ ↦ ∑ U : {U : Submodule (ZMod 2) V // Module.finrank (ZMod 2) U = k}, f U.val) _

/-- Nonzero actual subspaces decompose into exactly the positive rank bins. -/
theorem binary_nonzero_subspace_sum_by_rank {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [Finite V] (f : Submodule (ZMod 2) V → ℝ) :
    ∑ U : {U : Submodule (ZMod 2) V // U ≠ ⊥}, f U.val =
      ∑ k ∈ Finset.Icc 1 (Module.finrank (ZMod 2) V),
        ∑ U : {U : Submodule (ZMod 2) V // Module.finrank (ZMod 2) U = k}, f U.val := by
  classical
  let s := Finset.Icc 1 (Module.finrank (ZMod 2) V)
  let b : {U : Submodule (ZMod 2) V // U ≠ ⊥} → s :=
    fun U ↦ ⟨Module.finrank (ZMod 2) U.val,Finset.mem_Icc.mpr
      ⟨Submodule.one_le_finrank_iff.mpr U.property,U.val.finrank_le⟩⟩
  calc
    _ = ∑ k : s, ∑ U : {U // b U = k}, f U.val.val :=
      (Fintype.sum_fiberwise b (fun U ↦ f U.val)).symm
    _ = ∑ k : s, ∑ U : {U : Submodule (ZMod 2) V // Module.finrank (ZMod 2) U = k.val},
        f U.val := by
      apply Finset.sum_congr rfl
      intro k hk
      let e : {U // b U = k} ≃
          {U : Submodule (ZMod 2) V // Module.finrank (ZMod 2) U = k.val} :=
        { toFun := fun U ↦ ⟨U.val.val,congrArg Subtype.val U.property⟩
          invFun := fun U ↦ ⟨⟨U.val,Submodule.one_le_finrank_iff.mp (by
            rw [U.property]
            exact (Finset.mem_Icc.mp k.property).1)⟩,Subtype.ext U.property⟩
          left_inv := fun _ ↦ rfl
          right_inv := fun _ ↦ rfl }
      exact Fintype.sum_equiv e _ _ (fun _ ↦ rfl)
    _ = _ := Finset.sum_coe_sort s
      (fun k : ℕ ↦ ∑ U : {U : Submodule (ZMod 2) V // Module.finrank (ZMod 2) U = k}, f U.val)

/-- The exact rank-bin cardinality in any finite binary space, expressed in
the reals for use with weighted incidence inequalities. -/
theorem binary_subspace_rank_card {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [Finite V] (k : ℕ) (hk : k ≤ Module.finrank (ZMod 2) V) :
    (Nat.card {U : Submodule (ZMod 2) V // Module.finrank (ZMod 2) U = k} : ℝ) =
      (binaryGaussianCoefficient (Module.finrank (ZMod 2) V) k : ℝ) := by
  exact_mod_cast binary_rank_count_eq_finrank (E := V) k hk

end SymmetricSubgroupAsymptotics
