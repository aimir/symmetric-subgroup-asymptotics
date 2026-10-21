import SymmetricSubgroupAsymptotics.FiniteCyclicNormalizerCardBound

/-! Exact divisibility for the actual normalizer conjugation homomorphism.
This retains prime valuations, unlike a mere normalizer order inequality. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics

theorem normalizer_card_dvd_centralizer_mul_aut
    {G : Type*} [Group G] [Finite G] (H : Subgroup G) :
    Nat.card (Subgroup.normalizer (H : Set G)) ∣
      Nat.card (Subgroup.centralizer (H : Set G)) * Nat.card (MulAut H) := by
  let f := H.normalizerMonoidHom
  have hk : Nat.card f.ker = Nat.card (Subgroup.centralizer (H : Set G)) := by
    change Nat.card H.normalizerMonoidHom.ker = _
    rw [H.normalizerMonoidHom_ker]
    exact Nat.card_congr
      (Subgroup.subgroupOfEquivOfLe (Subgroup.centralizer_le_normalizer (H : Set G))).toEquiv
  have hr := f.range.card_subgroup_dvd_card
  have hm : Nat.card f.ker * Nat.card f.range =
      Nat.card (Subgroup.normalizer (H : Set G)) := by
    rw [←Subgroup.index_ker,f.ker.card_mul_index]
  rw [hk] at hm
  rw [←hm]
  exact Nat.mul_dvd_mul_left _ hr

end SymmetricSubgroupAsymptotics
