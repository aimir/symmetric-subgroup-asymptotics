import SymmetricSubgroupAsymptotics.PrimitiveSocleOneFactorOrdinaryRecurrence
import SymmetricSubgroupAsymptotics.PrimitiveSocleLeastIndexDegreeComparison
import SymmetricSubgroupAsymptotics.CFSGSufficientSimpleIndexBounds
import SymmetricSubgroupAsymptotics.ActualWreathUniformLocalOrderCost
import SymmetricSubgroupAsymptotics.CFSGCoarsePrimitiveNumerics
import SymmetricSubgroupAsymptotics.LinearLogOrdinaryGeneratorTail
import SymmetricSubgroupAsymptotics.External.CFSG.Parameters

/-! A one-factor ordinary tail from literal root generators and a genuine
root-star proper-index bound on the SAME simple factor. There is no
strict-coset induction at the minimum degree, and no global simple
two-generation assumption. Actual model consumers must supply their
displayed finite root generator set and proved proper-index theorem;
neither hypothesis is a desired aggregate bound. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.PrimitiveSocleOneFactorRootStarOrdinaryTail
open PrimitiveSocleRawStructure

variable {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]
    (D : NonaffineData G X)

theorem genRank_le_linear_log (hk : D.factorCount = 1)
    (q : CFSG.PrimePower) (r : ℕ) (hr : 2 ≤ r)
    (S : Finset D.Simple) (hS : Subgroup.closure (S : Set D.Simple) = ⊤)
    (hScard : S.card ≤ (2*r)*q.exponent)
    (hstar : ∀ H : Subgroup D.Simple, H ≠ ⊤ → q.order^(r-1) ≤ H.index)
    (ell : ℕ) (hell : LeastProperIndex D.Simple ell)
    (houter : SufficientOuterOrderBudget ell (Nat.card (Outer D.Simple))) :
    (MarkedC4.genRank G : ℝ) ≤ 5*Real.logb 2 (Nat.card X : ℝ)+3 := by
  obtain ⟨H,hH,hindex⟩ := hell.1
  have hell0 : 0 < ell := by
    have hh := H.one_lt_index_of_ne_top hH
    omega
  have hstarEll : q.order^(r-1) ≤ ell := by simpa only [hindex] using hstar H hH
  have hellDegree := PrimitiveSocleLeastIndexDegreeComparison.least_index_le_degree D ell hell
  have hfield : 2^q.exponent ≤ q.order :=
    Nat.pow_le_pow_left q.prime_isPrime.two_le q.exponent
  have hpow : 2^(q.exponent*(r-1)) ≤ Nat.card X := by
    calc
      _ = (2^q.exponent)^(r-1) := pow_mul 2 q.exponent (r-1)
      _ ≤ q.order^(r-1) := Nat.pow_le_pow_left hfield (r-1)
      _ ≤ ell := hstarEll
      _ ≤ Nat.card X := hellDegree
  let L := Real.logb 2 (Nat.card X : ℝ)
  have hdim : ((q.exponent*(r-1) : ℕ) : ℝ) ≤ L := by
    have hh := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
      (by positivity : (0 : ℝ) < (2 : ℝ)^(q.exponent*(r-1)))
      (show (2 : ℝ)^(q.exponent*(r-1)) ≤ (Nat.card X : ℝ) by exact_mod_cast hpow)
    simpa only [Real.logb_pow,Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2),
      mul_one] using hh
  have hcount : (2*r)*q.exponent ≤ 4*(q.exponent*(r-1)) := by
    have hh : r ≤ 2*(r-1) := by omega
    nlinarith only [Nat.mul_le_mul_right q.exponent hh]
  have hsRank : (MarkedC4.genRank D.Simple : ℝ) ≤ 4*L := by
    have hh : MarkedC4.genRank D.Simple ≤ 4*(q.exponent*(r-1)) :=
      (MarkedC4.genRank_le hS).trans (hScard.trans hcount)
    have hhR : (MarkedC4.genRank D.Simple : ℝ) ≤
        4*((q.exponent*(r-1) : ℕ) : ℝ) := by exact_mod_cast hh
    linarith only [hhR,hdim]
  have hout := houter.log_six_of_le hell0 hellDegree
  have hLcard : L ≤ (Nat.card X : ℝ) := CFSGCoarsePrimitiveNumerics.logb_nat_le_nat _
  have hout8 : (Nat.card (Outer D.Simple) : ℝ) ≤ 8*(Nat.card X : ℝ) := by
    nlinarith only [hout,hLcard,(Nat.cast_nonneg (Nat.card X) : (0 : ℝ) ≤ Nat.card X)]
  have hdegree0 : (0 : ℝ) < Nat.card X := by
    exact_mod_cast (hell0.trans_le hellDegree)
  have houtLog : Real.logb 2 (Nat.card (Outer D.Simple) : ℝ) ≤ 3+L := by
    have hh := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
      (by exact_mod_cast (Nat.card_pos (α := Outer D.Simple))) hout8
    rw [Real.logb_mul (by norm_num : (8 : ℝ) ≠ 0) hdegree0.ne'] at hh
    have h8 : Real.logb 2 (8 : ℝ) = 3 := by
      rw [show (8 : ℝ) = (2 : ℝ)^3 by norm_num,Real.logb_pow,
        Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2)]
      norm_num
    simpa only [h8] using hh
  have hOmega := (ActualWreathUniformLocalOrderCost.cardFactors_le_logb
    (Nat.card (Outer D.Simple)) (Nat.card_pos (α := Outer D.Simple)).ne').trans houtLog
  have hrec : (MarkedC4.genRank G : ℝ) ≤ (MarkedC4.genRank D.Simple : ℝ)+
      ArithmeticFunction.cardFactors (Nat.card (Outer D.Simple)) := by
    exact_mod_cast PrimitiveSocleOneFactorOrdinaryRecurrence.genRank_le_simple_add_outer_multiplicity D hk
  change (MarkedC4.genRank G : ℝ) ≤ 5*L+3
  linarith only [hrec,hsRank,hOmega]

theorem genRank_le_ceiling (hk : D.factorCount = 1)
    (q : CFSG.PrimePower) (r : ℕ) (hr : 2 ≤ r)
    (S : Finset D.Simple) (hS : Subgroup.closure (S : Set D.Simple) = ⊤)
    (hScard : S.card ≤ (2*r)*q.exponent)
    (hstar : ∀ H : Subgroup D.Simple, H ≠ ⊤ → q.order^(r-1) ≤ H.index)
    (ell : ℕ) (hell : LeastProperIndex D.Simple ell)
    (houter : SufficientOuterOrderBudget ell (Nat.card (Outer D.Simple)))
    (hn : 128 ≤ Nat.card X) :
    MarkedC4.genRank G ≤ traceyPermutationGeneratorCeiling (Nat.card X) := by
  have hh := genRank_le_linear_log D hk q r hr S hS hScard hstar ell hell houter
  have hreal := (hh.trans (LinearLogOrdinaryGeneratorTail.aggregate_le (Nat.card X) hn)).trans
    (Nat.le_ceil ((Nat.card X : ℝ)/Real.sqrt (Real.logb 2 (Nat.card X : ℝ))))
  change (MarkedC4.genRank G : ℝ) ≤
    (traceyPermutationGeneratorCeiling (Nat.card X) : ℝ) at hreal
  exact_mod_cast hreal

theorem exists_generating_finset (hk : D.factorCount = 1)
    (q : CFSG.PrimePower) (r : ℕ) (hr : 2 ≤ r)
    (S : Finset D.Simple) (hS : Subgroup.closure (S : Set D.Simple) = ⊤)
    (hScard : S.card ≤ (2*r)*q.exponent)
    (hstar : ∀ H : Subgroup D.Simple, H ≠ ⊤ → q.order^(r-1) ≤ H.index)
    (ell : ℕ) (hell : LeastProperIndex D.Simple ell)
    (houter : SufficientOuterOrderBudget ell (Nat.card (Outer D.Simple)))
    (hn : 128 ≤ Nat.card X) :
    ∃ U : Finset G, Subgroup.closure (U : Set G) = ⊤ ∧
      U.card ≤ traceyPermutationGeneratorCeiling (Nat.card X) := by
  obtain ⟨U,hU,hgen⟩ := MarkedC4.genRank_spec (G := G)
  exact ⟨U,hgen,hU.le.trans (genRank_le_ceiling D hk q r hr S hS hScard hstar ell hell houter hn)⟩

end SymmetricSubgroupAsymptotics.PrimitiveSocleOneFactorRootStarOrdinaryTail
