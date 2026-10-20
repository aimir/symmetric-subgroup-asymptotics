import SymmetricSubgroupAsymptotics.TransitiveNormalRankCardGap
import SymmetricSubgroupAsymptotics.BinaryPairCoordinateSubgroups

/-! The large proper normal images in the two degree-eight equality
branches have literal index two. The order comparison uses the normal
subgroup itself; there is no enlargement to an arbitrary maximal normal. -/
set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics

/-- A large proper normal in an original order-eight source has index two. -/
theorem normal_index_two_of_card_eight_normalGen_two
    {G : Type} [Group G] [Finite G]
    (hcard : Nat.card G = 8) (N : Subgroup G) [N.Normal]
    (hproper : N ≠ ⊤) (hrank : 2 ≤ MarkedC4.normalGen N) : N.index = 2 := by
  have hpow := MarkedC4.ActualNormalGeneratorDensity.two_pow_normalGen_le_card N
  have hfour : 4 ≤ Nat.card N :=
    (Nat.pow_le_pow_right (by decide : 0 < 2) hrank).trans hpow
  have hindex : 2 ≤ N.index := N.one_lt_index_of_ne_top hproper
  have hmul := N.card_mul_index
  rw [hcard] at hmul
  nlinarith

/-- Faithful transitivity rules out an order-eight rank-three proper
normal. Thus the corresponding order-thirty-two image has index two. -/
theorem transitive_degree_eight_card_thirty_two_normal_index_two
    {G X : Type} [Group G] [Finite G] [MulAction G X] [Finite X]
    [FaithfulSMul G X] [MulAction.IsPretransitive G X]
    (hG : IsPGroup 2 G) (hdegree : Nat.card X = 8)
    (hcard : Nat.card G = 32) (N : Subgroup G) [N.Normal]
    (hproper : N ≠ ⊤) (hrank : 3 ≤ MarkedC4.normalGen N) : N.index = 2 := by
  have hlarge : 8 < Nat.card N := by
    by_contra hsmall
    have hb := twoGroup_transitive_proper_normalGen_lt_exponent_of_card_le_degree
      hG 3 (by simpa only [show (2 : ℕ) ^ 3 = 8 from rfl] using hdegree)
      N hproper (by omega)
    omega
  have hindex : 2 ≤ N.index := N.one_lt_index_of_ne_top hproper
  have hmul := N.card_mul_index
  rw [hcard] at hmul
  have hlt : N.index < 4 := by nlinarith
  have hdvd : N.index ∣ 32 := hcard ▸ N.index_dvd_card
  have hcases : N.index = 2 ∨ N.index = 3 := by omega
  rcases hcases with htwo | hthree
  · exact htwo
  · rw [hthree] at hdvd
    norm_num at hdvd

namespace BinaryPairFrame

/-- Once the actual kernel is contained in N, its index is exactly the
index of its own top image. This transfers the index-two conclusion to
the original normal subgroup used in the head argument. -/
theorem normal_index_eq_actual_image_index
    {X I : Type} {U : Subgroup (Equiv.Perm X)}
    (F : BinaryPairFrame U I) (N : Subgroup U) (hker : F.top.ker ≤ N) :
    N.index = (N.map F.top.rangeRestrict).index := by
  apply Eq.symm
  apply Subgroup.index_map_eq N F.top.rangeRestrict_surjective
  simpa only [MonoidHom.ker_rangeRestrict] using hker

end BinaryPairFrame
end SymmetricSubgroupAsymptotics
