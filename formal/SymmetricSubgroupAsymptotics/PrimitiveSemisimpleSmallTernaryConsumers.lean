import SymmetricSubgroupAsymptotics.SemisimpleChiefWeightQuotientBound
import SymmetricSubgroupAsymptotics.SimpleSocleQuotientOrderBudget

/-! Bounded nonaffine ternary-chief consumers use only the actual outer
wreath embedding and ordinary simple-index bounds. No small simple-group
or primitive-group row classification is needed for these weight bounds. -/
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

theorem NonaffineData.small_ternaryChiefWeight_threeTenths
    (D : NonaffineData G X) (hindex : PublishedSimpleIndexBounds)
    (hs : Nat.card X<45) (c : ActualChiefSeries G) :
    10*actualChiefSeriesTernaryWeight c≤3*Nat.card X := by
  have hw := actualChiefSeriesTernaryWeight_le_semisimpleQuotient_factorization
    (finiteGroupSocle G) D.chart c
  obtain ⟨ell,hell⟩ := exists_leastProperIndex D.Simple
  have hf : 5≤ell := nonabelianSimple_leastProperIndex_five_le
    (fun h => D.noncommutative (isMulCommutative_iff.mpr h)) hell.1
  obtain ⟨horder,houter⟩ := hindex D.Simple D.noncommutative ell hell
  have hdegree := primitiveSocle_power_le_degree hf horder (D.degreeForm hell)
  rcases factorCount_one_or_two_small hf D.factorCount_pos hs hdegree with hk|⟨hk,he,h25⟩
  · obtain ⟨ell',_,hf',he',hlog⟩ := D.oneFactor_quotient_log_bound hk hindex
    have hq : Nat.card (G⧸finiteGroupSocle G)<27 := nat_lt_of_log_cube_bound
      (by omega) (by
        calc ell'^3≤44^3 := Nat.pow_le_pow_left (by omega) 3
             _ < 2^27 := by decide) hlog
    have hv := ternary_valuation_small_receipt.1 ⟨Nat.card (G⧸finiteGroupSocle G),hq⟩
    change (Nat.card (G⧸finiteGroupSocle G)).factorization 3 ≤ 2 at hv
    by_cases hn : 7≤Nat.card X
    · omega
    · have hq9 : Nat.card (G⧸finiteGroupSocle G)<9 := nat_lt_of_log_cube_bound
        (by omega) (by
          calc ell'^3≤6^3 := Nat.pow_le_pow_left (by omega) 3
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

end SymmetricSubgroupAsymptotics.PrimitiveSocleRawStructure
