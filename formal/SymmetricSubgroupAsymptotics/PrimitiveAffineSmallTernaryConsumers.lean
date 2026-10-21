import SymmetricSubgroupAsymptotics.PrimitiveAffineSmallTernaryNumerics
import SymmetricSubgroupAsymptotics.PrimitiveAffineHeadOrderBudget
import SymmetricSubgroupAsymptotics.ChiefTernaryOrderBound

/-! Complete bounded affine ternary-weight and strict-head consumers from
literal translation degree and the elementary faithful linear divisor.
There is no primitive catalogue or local classification premise. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.PrimitiveAffineProfile

variable {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]
    [FaithfulSMul G X] [Nontrivial X]
    (P : PrimitiveAffineProfile G X) (hp : MulAction.IsPreprimitive G X)

include P hp

theorem small_ternaryChiefWeight_threeTenths
    (hs : Nat.card X<45) (hf : 4≤Nat.card X) (h9 : Nat.card X≠9)
    (c : ActualChiefSeries G) : 10*actualChiefSeriesTernaryWeight c≤3*Nat.card X := by
  obtain ⟨p,d,hp',hd,hdegree,hdiv,hne⟩ := exists_prime_dimension_order_divisor P hp
  have hv := (Nat.factorization_le_iff_dvd Nat.card_pos.ne' hne).mpr hdiv 3
  have hb := (fullAffineOrder_small_ternary_bounds hp' hd
    (by rwa [←hdegree])).1 (by rwa [←hdegree]) (by rwa [←hdegree])
  have hw := actualChiefSeriesTernaryWeight_le_order c
  rw [←hdegree] at hb
  omega

theorem small_ternaryRelativeHead_strict
    (hs : Nat.card X<45) (h3 : Nat.card X≠3) (h4 : Nat.card X≠4)
    (N : Subgroup G) [N.Normal] :
    20*Module.finrank (ZMod 3) (primeRelativeCharacters 3 N)<3*Nat.card X := by
  obtain ⟨p,d,hp',hd,hdegree,hdiv,hne⟩ := exists_prime_dimension_order_divisor P hp
  have hv := (Nat.factorization_le_iff_dvd Nat.card_pos.ne' hne).mpr hdiv 3
  have hh := P.relativeHead_add_degreeFactorization_budget hp 3 h3 N
  have hb := (fullAffineOrder_small_ternary_bounds hp' hd
    (by rwa [←hdegree])).2.1 (by rwa [←hdegree]) (by rwa [←hdegree])
  rw [←hdegree] at hb
  omega

theorem degreeNine_ternaryChiefWeight_oneThird
    (h9 : Nat.card X=9) (c : ActualChiefSeries G) :
    3*actualChiefSeriesTernaryWeight c≤Nat.card X := by
  obtain ⟨p,d,hp',hd,hdegree,hdiv,hne⟩ := exists_prime_dimension_order_divisor P hp
  have hv := (Nat.factorization_le_iff_dvd Nat.card_pos.ne' hne).mpr hdiv 3
  have hb := (fullAffineOrder_small_ternary_bounds hp' hd
    (by rw [←hdegree,h9]; decide)).2.2 (hdegree.symm.trans h9)
  have hw := actualChiefSeriesTernaryWeight_le_order c
  rw [←hdegree] at hb
  omega

end SymmetricSubgroupAsymptotics.PrimitiveAffineProfile
