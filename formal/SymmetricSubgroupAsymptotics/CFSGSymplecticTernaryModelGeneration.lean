import SymmetricSubgroupAsymptotics.CFSGSymplecticTernaryGeneration
import SymmetricSubgroupAsymptotics.CFSGSymplecticProjectiveRealization
import SymmetricSubgroupAsymptotics.CFSGSimpleGenerationReduction

/-! Transfer the actual ternary elementary pair through the original
central quotient and checked Serre-model equivalence. This includes C2(3). -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGSymplecticTernaryModelGeneration
open CFSGSymplecticSerreMatrices CFSGSymplecticTernaryGeneration

theorem projective_exists_generating_pair {K : Type} [Field K] [Finite K]
    (hcard : Nat.card K = 3) (s : ℕ) :
    ∃ x y : elementaryProjective K (s + 2),
      Subgroup.closure ({x, y} : Set (elementaryProjective K (s + 2))) = ⊤ := by
  obtain ⟨x, y, hxy⟩ := elementary_exists_generating_pair hcard s
  let pi := QuotientGroup.mk' (Subgroup.center (elementaryRootGroup K (s + 2)))
  refine ⟨pi x, pi y, ?_⟩
  have he := congrArg (Subgroup.map pi) hxy
  simpa only [MonoidHom.map_closure, Set.image_insert_eq, Set.image_singleton,
    Subgroup.map_top_of_surjective pi (QuotientGroup.mk'_surjective _)] using he

end SymmetricSubgroupAsymptotics.CFSGSymplecticTernaryModelGeneration

namespace SymmetricSubgroupAsymptotics.CFSGReduction
open CFSGGeneration CFSGSymplecticSerreMatrices CFSGSymplecticTernaryModelGeneration

theorem typeC_ternary_twoGenerated (s : ℕ) (q : CFSG.PrimePower)
    (hq : q.order = 3) [IsSimpleGroup (CFSG.Models.C (s + 2) q)] :
    TwoGenerated (CFSG.Models.C (s + 2) q) := by
  have hcard : Nat.card q.Field = 3 := q.card_field.trans hq
  obtain ⟨x, y, hxy⟩ := projective_exists_generating_pair (K := q.Field) hcard s
  let e := serreProjectiveEquivElementaryProjective q.Field (s + 1)
  refine ⟨{e.symm x, e.symm y}, ?_, Finset.card_le_two⟩
  have he := congrArg (Subgroup.map e.symm.toMonoidHom) hxy
  simpa only [MonoidHom.map_closure, Set.image_insert_eq, Set.image_singleton,
    Subgroup.map_top_of_surjective e.symm.toMonoidHom e.symm.surjective,
    Finset.coe_insert, Finset.coe_singleton] using he

theorem typeC_ternary_twoGenerated_rank (r : ℕ) (q : CFSG.PrimePower)
    (hr : 2 ≤ r) (hq : q.order = 3) [IsSimpleGroup (CFSG.Models.C r q)] :
    TwoGenerated (CFSG.Models.C r q) := by
  have he : r = (r - 2) + 2 := (Nat.sub_add_cancel hr).symm
  letI : IsSimpleGroup (CFSG.Models.C ((r - 2) + 2) q) := by
    rw [← he]
    infer_instance
  have ht := typeC_ternary_twoGenerated (r - 2) q hq
  rw [← he] at ht
  exact ht

end SymmetricSubgroupAsymptotics.CFSGReduction
