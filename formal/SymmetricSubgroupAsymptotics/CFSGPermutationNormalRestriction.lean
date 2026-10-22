import SymmetricSubgroupAsymptotics.CFSGPermutationSubsetProduct
import Mathlib.GroupTheory.Perm.MaximalSubgroups

/-! Restriction of an actual invariant permutation subgroup to an original
subset. If every permutation supported on that subset normalizes the source,
the literal restriction image is normal in its full symmetric group. -/
set_option autoImplicit false
noncomputable section
open scoped Classical Pointwise

namespace SymmetricSubgroupAsymptotics.CFSGPermutationNormalRestriction
open Equiv MulAction CFSGPermutationSubsetProduct

variable {X : Type*} [DecidableEq X]

def restrictionHom (P : Subgroup (Perm X)) (s : Set X)
    (hPs : P ≤ MulAction.stabilizer (Perm X) s) : P →* Perm s :=
  (MulAction.toPermHom (MulAction.stabilizer (Perm X) s) s).comp (Subgroup.inclusion hPs)

@[simp] theorem restrictionHom_apply (P : Subgroup (Perm X)) (s : Set X)
    (hPs : P ≤ MulAction.stabilizer (Perm X) s) (g : P) (x : s) :
    ((restrictionHom P s hPs g) x).val = g.val x.val := rfl

theorem restrictionHom_conjugate (P : Subgroup (Perm X)) (s : Set X)
    (hPs : P ≤ MulAction.stabilizer (Perm X) s) (t : Perm s) (g : P)
    (hN : splitEmbedding s (t, 1) ∈ Subgroup.normalizer (P : Set (Perm X))) :
    ∃ h : P, restrictionHom P s hPs h =
      t * restrictionHom P s hPs g * t⁻¹ := by
  let r := splitEmbedding s (t, (1 : Perm (sᶜ : Set X)))
  have hmem : r * g.val * r⁻¹ ∈ P :=
    (Subgroup.mem_normalizer_iff.mp hN g.val).mp g.property
  let h : P := ⟨r * g.val * r⁻¹, hmem⟩
  refine ⟨h, ?_⟩
  have hrinv : r⁻¹ = splitEmbedding s (t⁻¹, (1 : Perm (sᶜ : Set X))) := by
    change (splitEmbedding s (t, (1 : Perm (sᶜ : Set X))))⁻¹ = _
    rw [← map_inv]
    simp only [Prod.inv_mk, inv_one]
  apply Perm.ext
  intro x
  apply Subtype.ext
  change splitEmbedding s (t, (1 : Perm (sᶜ : Set X))) (g.val (r⁻¹ x.val)) =
    (t ((restrictionHom P s hPs g) (t⁻¹ x))).val
  rw [hrinv, splitEmbedding_apply_mem s t⁻¹ 1 x.property]
  have hy : g.val ((t⁻¹ x).val) ∈ s :=
    ((restrictionHom P s hPs g) (t⁻¹ x)).property
  rw [splitEmbedding_apply_mem s t 1 hy]
  rfl

theorem restriction_range_normal (P : Subgroup (Perm X)) (s : Set X)
    (hPs : P ≤ MulAction.stabilizer (Perm X) s)
    (hN : ∀ t : Perm s, splitEmbedding s (t, 1) ∈
      Subgroup.normalizer (P : Set (Perm X))) : (restrictionHom P s hPs).range.Normal := by
  refine ⟨?_⟩
  rintro _ ⟨g, rfl⟩ t
  exact restrictionHom_conjugate P s hPs t g (hN t)

end SymmetricSubgroupAsymptotics.CFSGPermutationNormalRestriction
