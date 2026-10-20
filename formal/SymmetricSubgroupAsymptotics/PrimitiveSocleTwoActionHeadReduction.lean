import SymmetricSubgroupAsymptotics.PrimitiveCompositionTwoActionHeadReceipt
import SymmetricSubgroupAsymptotics.SimpleLeastIndexCompositionChart
import SymmetricSubgroupAsymptotics.SimpleSocleQuotientOrderBudget
import SymmetricSubgroupAsymptotics.BoundedPrimitiveSocleHeadConsequences
import SymmetricSubgroupAsymptotics.PerfectSubdirect

/-! Actual simple-socle head budgets from two applications of the same
retained composition correspondence. No116-row socle locator is assumed.
The original full socle and its original quotient remain literal. -/
set_option autoImplicit false
noncomputable section
open scoped Classical IsMulCommutative
namespace SymmetricSubgroupAsymptotics.PrimitiveSocleRawStructure

variable {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]
    [FaithfulSMul G X] [Nontrivial X] [MulAction.IsPreprimitive G X]

theorem NonaffineData.oneFactor_small_quotient_ternaryBudget
    (D : NonaffineData G X) (hk : D.factorCount=1)
    (catalogue : PublishedPrimitiveCompositionCatalogueCorrespondence)
    (hindex : PublishedSimpleIndexBounds)
    (M : PrimitiveCompositionCatalogueMatch G X)
    (hkind : (primitiveCompositionBoundRow M.row).kind=.orderBound)
    (hn : PrimitiveSmallSocleHeadDegree (Nat.card X)) :
    (Nat.card X≠18 →
      20*(Nat.card (G⧸finiteGroupSocle G)).factorization 3<3*Nat.card X) ∧
    (Nat.card X=18 → (Nat.card (G⧸finiteGroupSocle G)).factorization 3=0) := by
  have hsmall : Nat.card X≤18 := by dsimp only [PrimitiveSmallSocleHeadDegree] at hn; omega
  obtain ⟨ell,hell,hfive,helln,hlog⟩ := D.oneFactor_quotient_log_bound hk hindex
  have hq : Nat.card (G⧸finiteGroupSocle G)<15 :=
    quotient_order_lt_fifteen_of_log (by omega) (by omega) hlog
  obtain ⟨H,_,hi,⟨T⟩⟩ := compositionMatch_at_leastIndex
    catalogue D.noncommutative hell (by omega)
  have ht : (primitiveCompositionBoundRow T.row).degree=ell :=
    T.degree_eq.trans (H.index_eq_card.symm.trans hi)
  have hsocle : Nat.card (finiteGroupSocle G)=Nat.card D.Simple :=
    Nat.card_congr (D.oneFactorEquiv hk).toEquiv
  have hfactor : Nat.card (G⧸finiteGroupSocle G)*Nat.card D.Simple=Nat.card G := by
    rw [←hsocle]
    exact (Subgroup.card_eq_card_quotient_mul_card_subgroup (finiteGroupSocle G)).symm
  letI : MulAction.IsPretransitive (finiteGroupSocle G) X := D.socle_transitive
  have hdiv : Nat.card X∣Nat.card D.Simple := by
    rw [←hsocle]
    exact degree_dvd_card_of_transitive_normal (X := X) (finiteGroupSocle G)
  have hreceipt := primitiveComposition_twoAction_smallHead_receipt M.row T.row
    (Nat.card (G⧸finiteGroupSocle G)) Nat.card_pos hq hkind
    (by simpa only [M.degree_eq] using hn)
    (by rwa [ht]) (by rwa [ht,M.degree_eq])
    (by rw [←T.card_eq_row,←M.card_eq_row]; exact hfactor)
    (by rw [M.degree_eq,←T.card_eq_row]; exact hdiv)
  simpa only [M.degree_eq] using hreceipt

theorem NonaffineData.oneFactor_ternaryHead_strict_from_composition
    (D : NonaffineData G X) (hk : D.factorCount=1)
    (catalogue : PublishedPrimitiveCompositionCatalogueCorrespondence)
    (hindex : PublishedSimpleIndexBounds)
    (M : PrimitiveCompositionCatalogueMatch G X)
    (hkind : (primitiveCompositionBoundRow M.row).kind=.orderBound)
    (hn : PrimitiveSmallSocleHeadDegree (Nat.card X)) (h18 : Nat.card X≠18)
    (N : Subgroup G) [N.Normal] :
    20*Module.finrank (ZMod 3) (primeRelativeCharacters 3 N)<3*Nat.card X := by
  letI : Group.IsPerfect D.Simple := simple_perfect_of_nonabelian D.noncommutative
  letI : Group.IsPerfect (finiteGroupSocle G) :=
    Group.IsPerfect.ofSurjective (f := (D.oneFactorEquiv hk).symm.toMonoidHom)
      (D.oneFactorEquiv hk).symm.surjective
  have hh := primeRelativeHead_le_quotientFactorization_of_perfect_unique
    3 (finiteGroupSocle G) (D.oneFactor_socle_le hk) N
  have hb := (D.oneFactor_small_quotient_ternaryBudget hk catalogue hindex M hkind hn).1 h18
  omega

theorem NonaffineData.oneFactor_ternaryHead_strict_of_degree_ge_fourteen
    (D : NonaffineData G X) (hk : D.factorCount=1)
    (hindex : PublishedSimpleIndexBounds)
    (hf : 14≤Nat.card X) (hs : Nat.card X<30)
    (N : Subgroup G) [N.Normal] :
    20*Module.finrank (ZMod 3) (primeRelativeCharacters 3 N)<3*Nat.card X := by
  letI : Group.IsPerfect D.Simple := simple_perfect_of_nonabelian D.noncommutative
  letI : Group.IsPerfect (finiteGroupSocle G) :=
    Group.IsPerfect.ofSurjective (f := (D.oneFactorEquiv hk).symm.toMonoidHom)
      (D.oneFactorEquiv hk).symm.surjective
  have hh := primeRelativeHead_le_quotientFactorization_of_perfect_unique
    3 (finiteGroupSocle G) (D.oneFactor_socle_le hk) N
  have hb := ternaryValuation_le_two_of_lt_fifteen _
    (D.oneFactor_quotient_order_lt_fifteen hk hindex hs)
  omega

theorem NonaffineData.oneFactor_degreeEighteen_head_eq_zero_from_composition
    (D : NonaffineData G X) (hk : D.factorCount=1)
    (catalogue : PublishedPrimitiveCompositionCatalogueCorrespondence)
    (hindex : PublishedSimpleIndexBounds)
    (M : PrimitiveCompositionCatalogueMatch G X)
    (hkind : (primitiveCompositionBoundRow M.row).kind=.orderBound)
    (hn : Nat.card X=18) (N : Subgroup G) [N.Normal] :
    Module.finrank (ZMod 3) (primeRelativeCharacters 3 N)=0 := by
  letI : Group.IsPerfect D.Simple := simple_perfect_of_nonabelian D.noncommutative
  letI : Group.IsPerfect (finiteGroupSocle G) :=
    Group.IsPerfect.ofSurjective (f := (D.oneFactorEquiv hk).symm.toMonoidHom)
      (D.oneFactorEquiv hk).symm.surjective
  have hh := primeRelativeHead_le_quotientFactorization_of_perfect_unique
    3 (finiteGroupSocle G) (D.oneFactor_socle_le hk) N
  have hs : PrimitiveSmallSocleHeadDegree (Nat.card X) := by
    dsimp only [PrimitiveSmallSocleHeadDegree]
    omega
  have hb := (D.oneFactor_small_quotient_ternaryBudget hk catalogue hindex M hkind hs).2 hn
  omega

end SymmetricSubgroupAsymptotics.PrimitiveSocleRawStructure
