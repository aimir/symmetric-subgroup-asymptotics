import SymmetricSubgroupAsymptotics.CFSGOrthogonalDBinaryGeneration
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDProjectiveRealization
import SymmetricSubgroupAsymptotics.CFSGSimpleGenerationReduction
import Mathlib.Algebra.CharP.CharAndCard

/-! Transfer the proved binary pair through the actual D central
quotient and the original, untransposed Serre projective model. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDBinaryModelGeneration
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDBinaryGeneration
variable {K : Type} [Field K] [CharP K 2]

theorem projective_exists_generating_pair (hcard : Nat.card K = 2) (s : ℕ) :
    ∃ x y : elementaryProjective K (s + 4),
      Subgroup.closure ({x, y} : Set (elementaryProjective K (s + 4))) = ⊤ := by
  obtain ⟨x, y, hxy⟩ := elementary_exists_generating_pair hcard s
  let pi := QuotientGroup.mk' (Subgroup.center (elementaryRootGroup K (s + 4)))
  refine ⟨pi x, pi y, ?_⟩
  have he := congrArg (Subgroup.map pi) hxy
  simpa only [MonoidHom.map_closure, Set.image_insert_eq, Set.image_singleton,
    Subgroup.map_top_of_surjective pi (QuotientGroup.mk'_surjective _)] using he

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDBinaryModelGeneration

namespace SymmetricSubgroupAsymptotics.CFSGReduction
open CFSGGeneration CFSGOrthogonalDSerreMatrices CFSGOrthogonalDBinaryModelGeneration

theorem typeD_binary_twoGenerated (s : ℕ) (q : CFSG.PrimePower) (hq : q.order = 2)
    [IsSimpleGroup (CFSG.Models.D (s + 4) q)] : TwoGenerated (CFSG.Models.D (s + 4) q) := by
  letI orthogonalDBinaryFieldFintype : Fintype q.Field := Fintype.ofFinite q.Field
  letI orthogonalDBinaryPrimeTwo : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcard : Nat.card q.Field = 2 := q.card_field.trans hq
  letI orthogonalDBinaryFieldCharTwo : CharP q.Field 2 := charP_of_card_eq_prime
    (by simpa only [Nat.card_eq_fintype_card] using hcard)
  obtain ⟨x, y, hxy⟩ := projective_exists_generating_pair (K := q.Field) hcard s
  let e := serreProjectiveEquivElementaryProjective q.Field s
  refine ⟨{e.symm x, e.symm y}, ?_, Finset.card_le_two⟩
  have he := congrArg (Subgroup.map e.symm.toMonoidHom) hxy
  simpa only [MonoidHom.map_closure, Set.image_insert_eq, Set.image_singleton,
    Subgroup.map_top_of_surjective e.symm.toMonoidHom e.symm.surjective,
    Finset.coe_insert, Finset.coe_singleton] using he

theorem typeD_binary_twoGenerated_rank (r : ℕ) (q : CFSG.PrimePower)
    (hr : 4 ≤ r) (hq : q.order = 2) [IsSimpleGroup (CFSG.Models.D r q)] :
    TwoGenerated (CFSG.Models.D r q) := by
  have he : r = (r - 4) + 4 := (Nat.sub_add_cancel hr).symm
  letI orthogonalDBinaryRankSimple : IsSimpleGroup (CFSG.Models.D ((r - 4) + 4) q) := by
    rw [← he]
    infer_instance
  have ht := typeD_binary_twoGenerated (r - 4) q hq
  rw [← he] at ht
  exact ht

end SymmetricSubgroupAsymptotics.CFSGReduction
