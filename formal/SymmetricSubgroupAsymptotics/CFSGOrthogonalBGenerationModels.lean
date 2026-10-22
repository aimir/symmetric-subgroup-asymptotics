import SymmetricSubgroupAsymptotics.CFSGOrthogonalBGenerationFiniteFields
import SymmetricSubgroupAsymptotics.CFSGOrthogonalBGenerationCharTwoModels

/-! Exact original type-B model generation. In odd characteristic the
actual natural pair descends through the centre and the checked original
Serre projective equivalence. Characteristic two uses the previously
proved actual action-image restriction to type C, with no scalar-commutant
claim for the odd-dimensional natural representation. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalBGenerationModels
open CFSGOrthogonalBSerreMatrices CFSGOrthogonalBGenerationFiniteFields
variable (K : Type) [Field K] [Finite K]

theorem projective_exists_generating_pair (h2 : (2 : K) ≠ 0) (s : ℕ)
    (hcard : 3 ≤ Nat.card K) :
    ∃ x y : elementaryProjective K (s + 3),
      Subgroup.closure ({x, y} : Set (elementaryProjective K (s + 3))) = ⊤ := by
  obtain ⟨x, y, hxy⟩ := elementary_exists_generating_pair K h2 s hcard
  let pi := QuotientGroup.mk' (Subgroup.center (elementaryRootGroup K (s + 3)))
  refine ⟨pi x, pi y, ?_⟩
  have he := congrArg (Subgroup.map pi) hxy
  simpa only [MonoidHom.map_closure, Set.image_insert_eq, Set.image_singleton,
    Subgroup.map_top_of_surjective pi (QuotientGroup.mk'_surjective _)] using he

end SymmetricSubgroupAsymptotics.CFSGOrthogonalBGenerationModels

namespace SymmetricSubgroupAsymptotics.CFSGReduction
open CFSGGeneration CFSGOrthogonalBSerreMatrices CFSGOrthogonalBGenerationModels

theorem typeB_odd_twoGenerated (s : ℕ) (q : CFSG.PrimePower) (hq : q.prime ≠ 2)
    [IsSimpleGroup (CFSG.Models.B (s + 3) q)] : TwoGenerated (CFSG.Models.B (s + 3) q) := by
  have h2 : (2 : q.Field) ≠ 0 := by
    intro he
    have hd : q.prime ∣ 2 := (CharP.cast_eq_zero_iff q.Field q.prime 2).mp he
    exact hq ((Nat.prime_dvd_prime_iff_eq q.prime_isPrime Nat.prime_two).mp hd)
  have hp : 3 ≤ q.prime := by have hh := q.prime_isPrime.two_le; omega
  have hqcard : 3 ≤ q.order := by
    change 3 ≤ q.prime ^ q.exponent
    exact hp.trans (Nat.le_self_pow (Nat.ne_of_gt q.exponent_pos) q.prime)
  have hcard : 3 ≤ Nat.card q.Field := by rw [q.card_field]; exact hqcard
  obtain ⟨x, y, hxy⟩ := projective_exists_generating_pair q.Field h2 s hcard
  let e := serreProjectiveEquivElementaryProjective q.Field (s + 2) h2
  refine ⟨{e.symm x, e.symm y}, ?_, Finset.card_le_two⟩
  have he := congrArg (Subgroup.map e.symm.toMonoidHom) hxy
  simpa only [MonoidHom.map_closure, Set.image_insert_eq, Set.image_singleton,
    Subgroup.map_top_of_surjective e.symm.toMonoidHom e.symm.surjective,
    Finset.coe_insert, Finset.coe_singleton] using he

theorem typeB_twoGenerated (s : ℕ) (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.B (s + 3) q)] : TwoGenerated (CFSG.Models.B (s + 3) q) := by
  by_cases hq : q.prime = 2
  · exact typeB_charTwo_twoGenerated (s + 3) (by omega) q hq
  · exact typeB_odd_twoGenerated s q hq

theorem typeB_twoGenerated_of_index (r : ℕ) (q : CFSG.PrimePower)
    (hr : 3 ≤ r) [IsSimpleGroup (CFSG.Models.B r q)] : TwoGenerated (CFSG.Models.B r q) := by
  have he : r = (r - 3) + 3 := (Nat.sub_add_cancel hr).symm
  letI orthogonalBGenerationRankSimple : IsSimpleGroup (CFSG.Models.B ((r - 3) + 3) q) := by
    rw [← he]
    infer_instance
  have ht := typeB_twoGenerated (r - 3) q
  rw [← he] at ht
  exact ht

end SymmetricSubgroupAsymptotics.CFSGReduction
