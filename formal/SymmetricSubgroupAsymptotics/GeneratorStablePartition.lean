import Mathlib.GroupTheory.GroupAction.Primitive
import Mathlib.Algebra.Group.Subgroup.Basic

/-! A small pointwise partition witness excludes primitivity of the exact
generated permutation group. The certificate preserves equality of labels,
so it works for both pair systems and larger block systems. -/

set_option autoImplicit false
noncomputable section
open scoped Pointwise

namespace SymmetricSubgroupAsymptotics.GeneratorStablePartition

variable {X I J : Type} (label : X → J)

def stabilizer : Subgroup (Equiv.Perm X) where
  carrier := {g | ∀ x y, label (g x) = label (g y) ↔ label x = label y}
  one_mem' := fun _ _ => Iff.rfl
  mul_mem' := by
    intro g h hg hh x y
    exact (hg (h x) (h y)).trans (hh x y)
  inv_mem' := by
    intro g hg x y
    change label (g.symm x) = label (g.symm y) ↔ label x = label y
    simpa only [Equiv.apply_symm_apply] using (hg (g.symm x) (g.symm y)).symm

variable (generators : I → Equiv.Perm X)
    (preserves : ∀ i x y,
      label (generators i x) = label (generators i y) ↔ label x = label y)

include preserves in
theorem closure_le_stabilizer : Subgroup.closure (Set.range generators) ≤ stabilizer label := by
  apply (Subgroup.closure_le (stabilizer label)).mpr
  rintro _ ⟨i, rfl⟩
  exact preserves i

include preserves in
theorem fibre_isBlock (x₀ : X) :
    MulAction.IsBlock (Subgroup.closure (Set.range generators))
      {x | label x = label x₀} := by
  apply MulAction.isBlock_iff_smul_eq_of_mem.mpr
  intro g a ha hga
  have hg := closure_le_stabilizer label generators preserves g.2
  change label a = label x₀ at ha
  change label (g.1 a) = label x₀ at hga
  ext x
  change (∃ y, label y = label x₀ ∧ g.1 y = x) ↔ label x = label x₀
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ((hg y a).mpr (hy.trans ha.symm)).trans hga
  · intro hx
    refine ⟨g.1.symm x, ?_, g.1.apply_symm_apply x⟩
    have he : label (g.1 (g.1.symm x)) = label (g.1 a) := by
      rw [g.1.apply_symm_apply]
      exact hx.trans hga.symm
    exact ((hg (g.1.symm x) a).mp he).trans ha

include preserves in
/-- Three distinguished points certify that one preserved fibre is neither
a singleton nor the entire point set. -/
theorem not_preprimitive (x y z : X) (hxy : x ≠ y)
    (hsame : label y = label x) (houtside : label z ≠ label x) :
    ¬ MulAction.IsPreprimitive (Subgroup.closure (Set.range generators)) X := by
  intro hp
  letI := hp
  rcases (fibre_isBlock label generators preserves x).subsingleton_or_eq_univ with hs | hu
  · exact hxy (hs rfl hsame)
  · apply houtside
    have hz : z ∈ ({a | label a = label x} : Set X) := by
      rw [hu]
      trivial
    exact hz

end SymmetricSubgroupAsymptotics.GeneratorStablePartition

end
