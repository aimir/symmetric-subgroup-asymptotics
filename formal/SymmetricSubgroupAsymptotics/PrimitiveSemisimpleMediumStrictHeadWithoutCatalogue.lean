import SymmetricSubgroupAsymptotics.PrimitiveSemisimpleSmallTernaryConsumers
import SymmetricSubgroupAsymptotics.PrimitiveOuterOrderRoundingGap
import SymmetricSubgroupAsymptotics.OriginalNormalChiefHead

/-! The bounded strict relative-head range14..33 follows from the actual
semisimple quotient and the original simple-index logarithm. This leaves
only genuinely small actions to the separate strict-head frontier. -/
set_option autoImplicit false
noncomputable section
open scoped Classical IsMulCommutative
namespace SymmetricSubgroupAsymptotics.PrimitiveSocleRawStructure
open OuterWreathPermutationCompression

private theorem valuation_receipt :
    (∀ q : Fin 16,q.val.factorization 3≤2) ∧
    (∀ q : Fin 73,q.val.factorization 3≤3) := by decide +kernel

theorem NonaffineData.ternaryHead_strict_fourteenToThirtyThree
    {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]
    (D : NonaffineData G X) (hindex : PublishedSimpleIndexBounds)
    (h14 : 14≤Nat.card X) (h33 : Nat.card X≤33)
    (N : Subgroup G) [N.Normal] :
    20*Module.finrank (ZMod 3) (primeRelativeCharacters 3 N)<3*Nat.card X := by
  let c := actualChiefSeries G
  have hh := (primeRelativeHead_le_actualChiefWeight N c).trans
    (actualChiefSeriesTernaryWeight_le_semisimpleQuotient_factorization
      (finiteGroupSocle G) D.chart c)
  obtain ⟨ell,hell⟩ := exists_leastProperIndex D.Simple
  have hf : 5≤ell := nonabelianSimple_leastProperIndex_five_le
    (fun h => D.noncommutative (isMulCommutative_iff.mpr h)) hell.1
  obtain ⟨horder,houter⟩ := hindex D.Simple D.noncommutative ell hell
  have hd := primitiveSocle_power_le_degree hf horder (D.degreeForm hell)
  have hk3 : D.factorCount<3 := by
    by_contra h
    have hk : 3≤D.factorCount := by omega
    have hp : 125≤ell^D.factorCount := calc
      125=5^3 := by decide
      _ ≤ ell^3 := Nat.pow_le_pow_left hf 3
      _ ≤ ell^D.factorCount := pow_le_pow_right₀ (by omega : 1≤ell) hk
    omega
  have hk : D.factorCount=1 ∨ D.factorCount=2 := by
    have := D.factorCount_pos
    omega
  rcases hk with hk|hk
  · obtain ⟨ell',_,hf',he',hlog⟩ := D.oneFactor_quotient_log_bound hk hindex
    have hpow : 2^Nat.card (G⧸finiteGroupSocle G)≤35937 :=
      (quotientOrder_twoPow_le_cube_of_log (by omega) hlog).trans
        (by simpa using Nat.pow_le_pow_left (by omega : ell'≤33) 3)
    have hq : Nat.card (G⧸finiteGroupSocle G)<16 := by
      by_contra h
      have hb : 65536≤35937 := calc
        65536=2^16 := by decide
        _ ≤ 2^Nat.card (G⧸finiteGroupSocle G) :=
          pow_le_pow_right₀ (by decide : 1≤(2 : ℕ)) (by omega)
        _ ≤ 35937 := hpow
      omega
    have hv := valuation_receipt.1 ⟨Nat.card (G⧸finiteGroupSocle G),hq⟩
    change (Nat.card (G⧸finiteGroupSocle G)).factorization 3≤2 at hv
    omega
  · have he5 : ell=5 := by
      by_contra h
      have he6 : 6≤ell := by omega
      have hp : 36≤Nat.card X := calc
        36=6^2 := by decide
        _ ≤ ell^2 := Nat.pow_le_pow_left he6 2
        _ = ell^D.factorCount := by rw [hk]
        _ ≤ Nat.card X := hd
      omega
    have h25 : 25≤Nat.card X := by simpa only [he5,hk] using hd
    have hpow : 2^Nat.card (Outer D.Simple)≤125 := by
      simpa only [he5] using quotientOrder_twoPow_le_cube_of_log (by omega) houter
    have ho : Nat.card (Outer D.Simple)≤6 := by
      by_contra h
      have hb : 128≤125 := calc
        128=2^7 := by decide
        _ ≤ 2^Nat.card (Outer D.Simple) :=
          pow_le_pow_right₀ (by decide : 1≤(2 : ℕ)) (by omega)
        _ ≤ 125 := hpow
      omega
    have hq := Nat.card_le_card_of_injective D.quotientEmbedding D.quotientEmbedding_injective
    have hW : Nat.card (Wreath (Outer D.Simple) D.factorCount)=
        Nat.card (Outer D.Simple)^2*2 := by
      simp only [PermutationalWreathProduct.natCard_eq,Nat.card_fin,Nat.card_perm,hk]
      norm_num [Nat.factorial]
    have hq72 : Nat.card (G⧸finiteGroupSocle G)≤72 := calc
      _ ≤ Nat.card (Outer D.Simple)^2*2 := hq.trans_eq hW
      _ ≤ 6^2*2 := Nat.mul_le_mul_right _ (Nat.pow_le_pow_left ho 2)
      _ = 72 := by decide
    have hv := valuation_receipt.2 ⟨Nat.card (G⧸finiteGroupSocle G),by omega⟩
    change (Nat.card (G⧸finiteGroupSocle G)).factorization 3≤3 at hv
    omega

end SymmetricSubgroupAsymptotics.PrimitiveSocleRawStructure
