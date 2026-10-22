import SymmetricSubgroupAsymptotics.CFSGSufficientPrimitiveSocleQuotient
import SymmetricSubgroupAsymptotics.SemisimpleChiefWeightQuotientBound
import SymmetricSubgroupAsymptotics.PrimitiveSemisimpleMediumStrictHeadWithoutCatalogue

/-! The original bounded ternary targets follow from the sufficient hybrid.
The newly relaxed least-index range starts at27, where valuation at most
three is already enough. Smaller indices retain the old sharp arithmetic;
no original chief series or normal subgroup is replaced. -/
set_option autoImplicit false
noncomputable section
open scoped Classical IsMulCommutative
namespace SymmetricSubgroupAsymptotics.PrimitiveSocleRawStructure
open OuterWreathPermutationCompression

private theorem nat_lt_of_log_cube_bound {q ell b : ℕ}
    (hell : 0<ell) (hp : ell^3<2^b)
    (hq : (q : ℝ)≤3*Real.logb 2 ell) : q<b := by
  have hpR : (ell : ℝ)^3<(2 : ℝ)^b := by exact_mod_cast hp
  have hl := Real.logb_lt_logb (by norm_num : (1 : ℝ)<2)
    (pow_pos (by exact_mod_cast hell) 3) hpR
  simp only [Real.logb_pow,
    Real.logb_self_eq_one (by norm_num : (1 : ℝ)<2),mul_one] at hl
  have hr : (q : ℝ)<b := hq.trans_lt hl
  exact_mod_cast hr

private theorem ternary_valuation_small_receipt :
    (∀ q : Fin 27,q.val.factorization 3≤2) ∧
    (∀ q : Fin 9,q.val.factorization 3≤1) ∧
    (∀ q : Fin 129,q.val.factorization 3≤4) := by decide +kernel

private theorem factorCount_one_or_two_small {ell k n : ℕ}
    (hell : 5≤ell) (hk : 0<k) (hn : n<45) (hd : ell^k≤n) :
    k=1 ∨ (k=2 ∧ ell≤6 ∧ 25≤n) := by
  have hk3 : k<3 := by
    by_contra h
    have h3 : 3≤k := by omega
    have h125 : 125≤ell^k := calc
      125=5^3 := by decide
      _ ≤ ell^3 := Nat.pow_le_pow_left hell 3
      _ ≤ ell^k := pow_le_pow_right₀ (by omega : 1≤ell) h3
    omega
  by_cases hone : k=1
  · exact Or.inl hone
  · have htwo : k=2 := by omega
    right
    refine ⟨htwo,?_,?_⟩
    · by_contra h
      have h7 : 7≤ell := by omega
      have h49 : 49≤ell^k := calc
        49=7^2 := by decide
        _ ≤ ell^2 := Nat.pow_le_pow_left h7 2
        _ = ell^k := by rw [htwo]
      omega
    · have h25 : 25≤ell^k := calc
        25=5^2 := by decide
        _ ≤ ell^2 := Nat.pow_le_pow_left hell 2
        _ = ell^k := by rw [htwo]
      omega

variable {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]

private theorem oneFactor_quotient_le_outer (D : NonaffineData G X)
    (hk : D.factorCount = 1) :
    Nat.card (G ⧸ finiteGroupSocle G) ≤ Nat.card (Outer D.Simple) := by
  have hw : Nat.card (Wreath (Outer D.Simple) D.factorCount) = Nat.card (Outer D.Simple) := by
    rw [hk]
    exact wreath_one_card (Outer D.Simple)
  exact (Nat.card_le_card_of_injective D.quotientEmbedding D.quotientEmbedding_injective).trans_eq hw

theorem NonaffineData.small_ternaryChiefWeight_threeTenths_of_sufficient
    (D : NonaffineData G X) (hindex : SufficientSimpleIndexBounds)
    (hs : Nat.card X < 45) (c : ActualChiefSeries G) :
    10 * actualChiefSeriesTernaryWeight c ≤ 3 * Nat.card X := by
  have hw := actualChiefSeriesTernaryWeight_le_semisimpleQuotient_factorization
    (finiteGroupSocle G) D.chart c
  obtain ⟨ell, _, hf, hdegree, hbudget⟩ := D.sufficient_degree_lower hindex
  by_cases hsmall : ell < 27
  · have houter := hbudget.log_three_of_small hsmall
    rcases factorCount_one_or_two_small hf D.factorCount_pos hs hdegree with hk|⟨hk,he,h25⟩
    · have he' : ell ≤ Nat.card X := by simpa only [hk, pow_one] using hdegree
      have hqOut := oneFactor_quotient_le_outer D hk
      have hlog : (Nat.card (G ⧸ finiteGroupSocle G) : ℝ) ≤ 3 * Real.logb 2 ell :=
        (by exact_mod_cast hqOut : (Nat.card (G ⧸ finiteGroupSocle G) : ℝ) ≤
          Nat.card (Outer D.Simple)).trans houter
      have hq : Nat.card (G⧸finiteGroupSocle G)<27 := nat_lt_of_log_cube_bound
        (by omega) (by
          calc ell^3≤44^3 := Nat.pow_le_pow_left (by omega) 3
               _ < 2^27 := by decide) hlog
      have hv := ternary_valuation_small_receipt.1 ⟨Nat.card (G⧸finiteGroupSocle G),hq⟩
      change (Nat.card (G⧸finiteGroupSocle G)).factorization 3 ≤ 2 at hv
      by_cases hn : 7≤Nat.card X
      · omega
      · have hq9 : Nat.card (G⧸finiteGroupSocle G)<9 := nat_lt_of_log_cube_bound
          (by omega) (by
            calc ell^3≤6^3 := Nat.pow_le_pow_left (by omega) 3
                 _ < 2^9 := by decide) hlog
        have hv1 := ternary_valuation_small_receipt.2.1 ⟨Nat.card (G⧸finiteGroupSocle G),hq9⟩
        change (Nat.card (G⧸finiteGroupSocle G)).factorization 3 ≤ 1 at hv1
        omega
    · have hOut : Nat.card (Outer D.Simple)<9 := nat_lt_of_log_cube_bound
        (by omega) (by
          calc ell^3≤6^3 := Nat.pow_le_pow_left he 3
               _ < 2^9 := by decide) houter
      have hq := Nat.card_le_card_of_injective D.quotientEmbedding D.quotientEmbedding_injective
      have hW : Nat.card (Wreath (Outer D.Simple) D.factorCount)=
          Nat.card (Outer D.Simple)^2*2 := by
        simp only [PermutationalWreathProduct.natCard_eq,Nat.card_fin,Nat.card_perm,hk]
        norm_num [Nat.factorial]
      have hq128 : Nat.card (G⧸finiteGroupSocle G)≤128 := by
        have ho8 : Nat.card (Outer D.Simple)≤8 := by omega
        calc
          _ ≤ Nat.card (Outer D.Simple)^2*2 := hq.trans_eq hW
          _ ≤ 8^2*2 := Nat.mul_le_mul_right _ (Nat.pow_le_pow_left ho8 2)
          _ = 128 := by decide
      have hv := ternary_valuation_small_receipt.2.2
        ⟨Nat.card (G⧸finiteGroupSocle G),by omega⟩
      change (Nat.card (G⧸finiteGroupSocle G)).factorization 3 ≤ 4 at hv
      omega
  · have h27 : 27 ≤ ell := by omega
    have hk : D.factorCount = 1 := by
      rcases factorCount_one_or_two_small hf D.factorCount_pos hs hdegree with hk | hk
      · exact hk
      · omega
    have he : ell ≤ Nat.card X := by simpa only [hk, pow_one] using hdegree
    have hbudgetQ := hbudget.mono (oneFactor_quotient_le_outer D hk)
    exact CFSGSufficientSimpleIndexNumerics.threeTenths_weight (by omega) (by omega)
      (hbudgetQ.log_six_of_le (by omega) he) hw

private theorem medium_valuation_receipt :
    (∀ q : Fin 16, q.val.factorization 3 ≤ 2) ∧
    (∀ q : Fin 73, q.val.factorization 3 ≤ 3) := by decide +kernel

theorem NonaffineData.ternaryHead_strict_fourteenToThirtyThree_of_sufficient
    (D : NonaffineData G X) (hindex : SufficientSimpleIndexBounds)
    (h14 : 14 ≤ Nat.card X) (h33 : Nat.card X ≤ 33)
    (N : Subgroup G) [N.Normal] :
    20 * Module.finrank (ZMod 3) (primeRelativeCharacters 3 N) < 3 * Nat.card X := by
  let c := actualChiefSeries G
  have hh := (primeRelativeHead_le_actualChiefWeight N c).trans
    (actualChiefSeriesTernaryWeight_le_semisimpleQuotient_factorization
      (finiteGroupSocle G) D.chart c)
  obtain ⟨ell, _, hf, hd, hb⟩ := D.sufficient_degree_lower hindex
  have hk3 : D.factorCount < 3 := by
    by_contra h
    have hk : 3 ≤ D.factorCount := by omega
    have hp : 125 ≤ ell ^ D.factorCount := calc
      125 = 5 ^ 3 := by decide
      _ ≤ ell ^ 3 := Nat.pow_le_pow_left hf 3
      _ ≤ ell ^ D.factorCount := pow_le_pow_right₀ (by omega : 1 ≤ ell) hk
    omega
  have hk : D.factorCount = 1 ∨ D.factorCount = 2 := by
    have := D.factorCount_pos
    omega
  rcases hk with hk | hk
  · have he : ell ≤ Nat.card X := by simpa only [hk, pow_one] using hd
    have hbQ := hb.mono (oneFactor_quotient_le_outer D hk)
    by_cases hs : ell < 27
    · have hlog := hbQ.log_three_of_small hs
      have hq : Nat.card (G ⧸ finiteGroupSocle G) < 16 :=
        nat_lt_of_log_cube_bound (by omega) (by
          calc ell ^ 3 ≤ 33 ^ 3 := Nat.pow_le_pow_left (by omega) 3
               _ < 2 ^ 16 := by decide) hlog
      have hv := medium_valuation_receipt.1 ⟨Nat.card (G ⧸ finiteGroupSocle G), hq⟩
      change (Nat.card (G ⧸ finiteGroupSocle G)).factorization 3 ≤ 2 at hv
      omega
    · exact CFSGSufficientSimpleIndexNumerics.strict_relative_head (by omega) h33
        (hbQ.log_six_of_le (by omega) he) hh
  · have he5 : ell = 5 := by
      by_contra h
      have he6 : 6 ≤ ell := by omega
      have hp : 36 ≤ Nat.card X := calc
        36 = 6 ^ 2 := by decide
        _ ≤ ell ^ 2 := Nat.pow_le_pow_left he6 2
        _ = ell ^ D.factorCount := by rw [hk]
        _ ≤ Nat.card X := hd
      omega
    have h25 : 25 ≤ Nat.card X := by simpa only [he5, hk] using hd
    have houter := hb.log_three_of_small (by omega)
    have ho : Nat.card (Outer D.Simple) < 7 :=
      nat_lt_of_log_cube_bound (by omega) (by rw [he5]; decide) houter
    have hq := Nat.card_le_card_of_injective D.quotientEmbedding D.quotientEmbedding_injective
    have hW : Nat.card (Wreath (Outer D.Simple) D.factorCount) =
        Nat.card (Outer D.Simple) ^ 2 * 2 := by
      simp only [PermutationalWreathProduct.natCard_eq, Nat.card_fin, Nat.card_perm, hk]
      norm_num [Nat.factorial]
    have hq72 : Nat.card (G ⧸ finiteGroupSocle G) ≤ 72 := calc
      _ ≤ Nat.card (Outer D.Simple) ^ 2 * 2 := hq.trans_eq hW
      _ ≤ 6 ^ 2 * 2 := Nat.mul_le_mul_right _ (Nat.pow_le_pow_left (by omega) 2)
      _ = 72 := by decide
    have hv := medium_valuation_receipt.2 ⟨Nat.card (G ⧸ finiteGroupSocle G), by omega⟩
    change (Nat.card (G ⧸ finiteGroupSocle G)).factorization 3 ≤ 3 at hv
    omega

end SymmetricSubgroupAsymptotics.PrimitiveSocleRawStructure
