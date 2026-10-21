import SymmetricSubgroupAsymptotics.CFSGOrthogonalDGenerationFiniteFields
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDBinaryModelGeneration

/-! Actual central-quotient and original untransposed type-D model
transport. The nonbinary pair and the previously proved binary pair cover
every prime-power field, with exactly the original rank-four guard. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDGenerationModels
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDGenerationFiniteFields
variable (K : Type) [Field K] [Finite K]

theorem projective_exists_generating_pair (s : ℕ) (hcard : 3 ≤ Nat.card K) :
    ∃ x y : elementaryProjective K (s + 4),
      Subgroup.closure ({x, y} : Set (elementaryProjective K (s + 4))) = ⊤ := by
  obtain ⟨x, y, hxy⟩ := elementary_exists_generating_pair K s hcard
  let pi := QuotientGroup.mk' (Subgroup.center (elementaryRootGroup K (s + 4)))
  refine ⟨pi x, pi y, ?_⟩
  have he := congrArg (Subgroup.map pi) hxy
  simpa only [MonoidHom.map_closure, Set.image_insert_eq, Set.image_singleton,
    Subgroup.map_top_of_surjective pi (QuotientGroup.mk'_surjective _)] using he

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDGenerationModels

namespace SymmetricSubgroupAsymptotics.CFSGReduction
open CFSGGeneration CFSGOrthogonalDSerreMatrices CFSGOrthogonalDGenerationModels

theorem typeD_nonbinary_twoGenerated (s : ℕ) (q : CFSG.PrimePower) (hq : 3 ≤ q.order)
    [IsSimpleGroup (CFSG.Models.D (s + 4) q)] : TwoGenerated (CFSG.Models.D (s + 4) q) := by
  have hcard : 3 ≤ Nat.card q.Field := by rw [q.card_field]; exact hq
  obtain ⟨x, y, hxy⟩ := projective_exists_generating_pair q.Field s hcard
  let e := serreProjectiveEquivElementaryProjective q.Field s
  refine ⟨{e.symm x, e.symm y}, ?_, Finset.card_le_two⟩
  have he := congrArg (Subgroup.map e.symm.toMonoidHom) hxy
  simpa only [MonoidHom.map_closure, Set.image_insert_eq, Set.image_singleton,
    Subgroup.map_top_of_surjective e.symm.toMonoidHom e.symm.surjective,
    Finset.coe_insert, Finset.coe_singleton] using he

theorem typeD_twoGenerated (s : ℕ) (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.D (s + 4) q)] : TwoGenerated (CFSG.Models.D (s + 4) q) := by
  by_cases hq : q.order = 2
  · exact typeD_binary_twoGenerated s q hq
  · have hq2 : 2 ≤ q.order := by
      change 2 ≤ q.prime ^ q.exponent
      have hh := Nat.one_lt_pow (Nat.ne_of_gt q.exponent_pos) q.prime_isPrime.one_lt
      omega
    exact typeD_nonbinary_twoGenerated s q (by omega)

theorem typeD_twoGenerated_of_index (r : ℕ) (q : CFSG.PrimePower)
    (hr : 4 ≤ r) [IsSimpleGroup (CFSG.Models.D r q)] : TwoGenerated (CFSG.Models.D r q) := by
  have he : r = (r - 4) + 4 := (Nat.sub_add_cancel hr).symm
  letI orthogonalDGenerationRankSimple : IsSimpleGroup (CFSG.Models.D ((r - 4) + 4) q) := by
    rw [← he]
    infer_instance
  have ht := typeD_twoGenerated (r - 4) q
  rw [← he] at ht
  exact ht

end SymmetricSubgroupAsymptotics.CFSGReduction
