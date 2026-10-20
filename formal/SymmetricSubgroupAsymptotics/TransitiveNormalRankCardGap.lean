import SymmetricSubgroupAsymptotics.PGroupNormalGeneratorCharacterEquality
import SymmetricSubgroupAsymptotics.PrimeRelativeRadicalPresentation
import SymmetricSubgroupAsymptotics.FaithfulTransitiveCentralCard
import SymmetricSubgroupAsymptotics.MarkedC4ActualNormalGeneratorDensity

/-! Saturating the order bound on an actual relative binary head forces
centrality. In a faithful transitive original action a central subgroup of
full point-set cardinality forces regularity, so a proper normal cannot
saturate that head. This reduces sharp finite checks to genuinely larger
normal subgroups, without a normal table or catalogue premise. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical commutatorElement

namespace SymmetricSubgroupAsymptotics

/-- A proper original normal whose order is at most the original degree
has normal rank strictly smaller than the binary degree exponent. -/
theorem twoGroup_transitive_proper_normalGen_lt_exponent_of_card_le_degree
    {G X : Type} [Group G] [Finite G] [MulAction G X] [Finite X]
    [FaithfulSMul G X] [MulAction.IsPretransitive G X]
    (hG : IsPGroup 2 G) (k : ℕ) (hdegree : Nat.card X = 2 ^ k)
    (N : Subgroup G) [N.Normal] (hproper : N ≠ ⊤)
    (hNcard : Nat.card N ≤ Nat.card X) : MarkedC4.normalGen N < k := by
  have hpowpos : 0 < 2 ^ k := by positivity
  have hXpos : 0 < Nat.card X := by omega
  letI : Nonempty X := (Nat.card_pos_iff.mp hXpos).1
  let x : X := Classical.choice inferInstance
  by_contra hbad
  have hlow : k ≤ MarkedC4.normalGen N := by omega
  have hp := MarkedC4.ActualNormalGeneratorDensity.two_pow_normalGen_le_card N
  have hlowpow : 2 ^ k ≤ Nat.card N :=
    (Nat.pow_le_pow_right (by decide : 0 < 2) hlow).trans hp
  have hNexact : Nat.card N = 2 ^ k := by omega
  have hhigh : MarkedC4.normalGen N ≤ k :=
    (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp (hp.trans_eq hNexact)
  have hrank : MarkedC4.normalGen N = k := by omega
  have hfactor := primeRelativeRadical_card_factorization 2 N
  rw [← pGroup_normalGen_eq_primeRelativeHead 2 hG N, hrank, hNexact] at hfactor
  have hRcard : Nat.card (primeRelativeRadical 2 N) = 1 := by nlinarith
  have hRbot := (primeRelativeRadical 2 N).eq_bot_of_card_eq hRcard
  have hcentral (n : N) : (n : G) ∈ Subgroup.center G := by
    rw [Subgroup.mem_center_iff]
    intro g
    have hc := commutator_mem_primeRelativeRadical 2 N n g
    rw [hRbot] at hc
    exact (commutatorElement_eq_one_iff_mul_comm.mp (show ⁅(n : G), g⁆ = 1 from hc)).symm
  have hGcard := card_group_eq_points_of_central_card_ge
    N.subtype N.subtype_injective hcentral x (by omega : Nat.card X ≤ Nat.card N)
  exact hproper (N.eq_top_of_card_eq (hNexact.trans (hdegree.symm.trans hGcard.symm)))

/-- In particular the small-order original eight-point sources need no
proper-normal rank table: every proper normal has rank at most two. -/
theorem twoGroup_transitive_degree_eight_small_order_proper_normalGen_le_two
    {G X : Type} [Group G] [Finite G] [MulAction G X] [Finite X]
    [FaithfulSMul G X] [MulAction.IsPretransitive G X]
    (hG : IsPGroup 2 G) (hdegree : Nat.card X = 8) (horder : Nat.card G ≤ 16)
    (N : Subgroup G) [N.Normal] (hproper : N ≠ ⊤) : MarkedC4.normalGen N ≤ 2 := by
  have hind : 2 ≤ N.index := N.one_lt_index_of_ne_top hproper
  have hm := N.card_mul_index
  have hpos : 0 < Nat.card N := Nat.card_pos
  have hNcard : Nat.card N ≤ Nat.card X := by nlinarith
  have hb := twoGroup_transitive_proper_normalGen_lt_exponent_of_card_le_degree
    hG 3 hdegree N hproper hNcard
  omega

end SymmetricSubgroupAsymptotics
