import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexPlaneFamilyAction
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexPositiveChains
import SymmetricSubgroupAsymptotics.CFSGInnerActionFaithfulness

/-! Faithfulness of the SAME projective D automorphism geometry, when
the actual quotient is simple. One literal original chain root moves
the original positive two-plane, so the inner action is nontrivial.
No full isometry-group equality or automorphism lifting is used. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexPlaneFamilyAction
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDIndexPlaneRootLine
open CFSGOrthogonalDIndexRootPlaneImage CFSGOrthogonalDIndexSingularRootPlanes
open CFSGOrthogonalDIndexProjectiveRootFamily CFSGOrthogonalDIndexProjectiveUnipotent
open CFSGOrthogonalDIndexPositiveChains CFSGOrthogonalDGenerationRootArrays
open CFSGOrthogonalDIndexFlagVectors
variable (K : Type) [Field K]

theorem singularLabel_inner_plane (s : ℕ) (g h : elementaryRootGroup K (s + 4)) :
    singularLabel K s (singularPlane K s (g * h)) =
      (singularLabel K s (singularPlane K s h)).map (MulAut.conj (projection K s g)).toMonoidHom := by
  rw [singularLabel_plane, singularLabel_plane]
  change (projectiveHighestRootLine K s).map (MulAut.conj (projection K s (g * h))).toMonoidHom =
    ((projectiveHighestRootLine K s).map (MulAut.conj (projection K s h)).toMonoidHom).map
      (MulAut.conj (projection K s g)).toMonoidHom
  rw [Subgroup.map_map]
  congr 1
  apply MonoidHom.ext
  intro x
  simp [MulAut.conj_apply, map_mul, mul_assoc]

theorem singularAction_inner_plane [Finite K] (p : ℕ) [Fact p.Prime] [CharP K p]
    (s : ℕ) (g h : elementaryRootGroup K (s + 4)) :
    singularActionHom K p s (MulAut.conj (projection K s g)) (singularPlane K s h) =
      singularPlane K s (g * h) := by
  apply singularLabel_injective K s
  rw [singularLabel_action]
  exact (singularLabel_inner_plane K s g h).symm

theorem exists_moved_original_plane (s : ℕ) :
    ∃ g : elementaryRootGroup K (s + 4), singularPlane K s g ≠ singularPlane K s 1 := by
  let i : Fin (s + 4) := ⟨2, by omega⟩
  have hi : i ≠ 0 := by
    intro he
    have hh := congrArg Fin.val he
    change 2 = 0 at hh
    omega
  let g := chainElement K (s + 4) i 0 hi 1
  have hcoord : ((g.val : Mat K (s + 4)) *ᵥ firstVector K s) (Sum.inl i) = 1 := by
    change (((chainElement K (s + 4) i 0 hi 1).val : Mat K (s + 4)) *ᵥ
      Pi.single (Sum.inl 0) 1) (Sum.inl i) = 1
    rw [chainElement_val, Matrix.mulVec_single_one]
    simp [chainArray, Matrix.one_apply, Matrix.single_apply, hi, Ne.symm hi]
  have hstandard : ∀ x ∈ standardRootPlane K s, x (Sum.inl i) = 0 := by
    intro x hx
    obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.mp hx
    simp [firstVector, secondVector, secondIndex, i, Pi.single_apply, Fin.ext_iff]
  have hbase : conjugateRootPlane K s (1 : elementaryRootGroup K (s + 4)) = standardRootPlane K s := by
    rw [conjugateRootPlane_eq_map_standard]
    change (standardRootPlane K s).map (Matrix.mulVecLin (1 : Mat K (s + 4))) = _
    rw [Matrix.mulVecLin_one, Submodule.map_id]
  refine ⟨g, ?_⟩
  intro he
  have hp := congrArg Subtype.val he
  change conjugateRootPlane K s g = conjugateRootPlane K s (1 : elementaryRootGroup K (s + 4)) at hp
  have hm : (g.val : Mat K (s + 4)) *ᵥ firstVector K s ∈ conjugateRootPlane K s g :=
    Submodule.subset_span (Or.inl rfl)
  rw [hp, hbase] at hm
  have hz := hstandard _ hm
  rw [hcoord] at hz
  exact one_ne_zero hz

theorem singularActionHom_injective [Finite K] (p : ℕ) [Fact p.Prime] [CharP K p]
    (s : ℕ) [IsSimpleGroup (elementaryProjective K (s + 4))] :
    Function.Injective (singularActionHom K p s) := by
  apply CFSGInnerActionFaithfulness.injective_of_inner_nontrivial
  obtain ⟨g, hg⟩ := exists_moved_original_plane K s
  refine ⟨projection K s g, ?_⟩
  intro he
  have hm := singularAction_inner_plane K p s g 1
  rw [he] at hm
  have hp : singularPlane K s 1 = singularPlane K s g := by
    simpa only [Equiv.Perm.one_apply, mul_one] using hm
  exact hg hp.symm

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexPlaneFamilyAction
