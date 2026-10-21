import SymmetricSubgroupAsymptotics.CFSGSymplecticLargeFieldGeneration
import SymmetricSubgroupAsymptotics.CFSGSymplecticProjectiveRealization
import SymmetricSubgroupAsymptotics.CFSGSimpleGenerationReduction

/-! Transport the actual large-field elementary C pair through its
literal central quotient and the checked original Serre-model bridge.
No equality with the full symplectic matrix group is needed. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGSymplecticSerreMatrices

theorem projective_large_field_exists_generating_pair (K : Type) [Field K] [Finite K]
    (hcard : 4 ≤ Nat.card K) (s : ℕ) :
    ∃ x y : elementaryProjective K (s + 2),
      Subgroup.closure ({x, y} : Set (elementaryProjective K (s + 2))) = ⊤ := by
  obtain ⟨x, y, hxy⟩ := elementary_large_field_exists_generating_pair K hcard s
  let pi := QuotientGroup.mk' (Subgroup.center (elementaryRootGroup K (s + 2)))
  refine ⟨pi x, pi y, ?_⟩
  have he := congrArg (Subgroup.map pi) hxy
  simpa only [MonoidHom.map_closure, Set.image_insert_eq, Set.image_singleton,
    Subgroup.map_top_of_surjective pi (QuotientGroup.mk'_surjective _)] using he

end SymmetricSubgroupAsymptotics.CFSGSymplecticSerreMatrices

namespace SymmetricSubgroupAsymptotics.CFSGReduction
open CFSGGeneration CFSGSymplecticSerreMatrices

theorem typeC_large_field_twoGenerated (r : ℕ) (hr : 2 ≤ r) (q : CFSG.PrimePower)
    (hq : 4 ≤ q.order) [IsSimpleGroup (CFSG.Models.C r q)] : TwoGenerated (CFSG.Models.C r q) := by
  classical
  obtain ⟨s, rfl⟩ : ∃ s : ℕ, r = s + 2 := ⟨r - 2, by omega⟩
  have hcard : 4 ≤ Nat.card q.Field := by rw [q.card_field]; exact hq
  obtain ⟨x, y, hxy⟩ := projective_large_field_exists_generating_pair q.Field hcard s
  let e : CFSG.Models.C (s + 2) q ≃* elementaryProjective q.Field (s + 2) :=
    serreProjectiveEquivElementaryProjective q.Field (s + 1)
  refine ⟨{e.symm x, e.symm y}, ?_, Finset.card_le_two⟩
  have he := congrArg (Subgroup.map e.symm.toMonoidHom) hxy
  simpa only [MonoidHom.map_closure, Set.image_insert_eq, Set.image_singleton,
    Subgroup.map_top_of_surjective e.symm.toMonoidHom e.symm.surjective,
    Finset.coe_insert, Finset.coe_singleton] using he

end SymmetricSubgroupAsymptotics.CFSGReduction
