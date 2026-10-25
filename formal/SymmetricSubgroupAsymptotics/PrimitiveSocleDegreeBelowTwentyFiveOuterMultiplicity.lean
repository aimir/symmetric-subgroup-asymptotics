import SymmetricSubgroupAsymptotics.PrimitiveSocleSmallDegreeOuterMultiplicity

/-! Actual degree geometry forces ONE socle factor below degree 25.
The sufficient packet at that same factor's least index bounds its
outer prime multiplicity by three. No ordinary generation claim is
assumed, and the conclusion is also available for the smaller degrees. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.PrimitiveSocleDegreeBelowTwentyFiveOuterMultiplicity
open PrimitiveSocleRawStructure

theorem factor_and_outer_multiplicity
    {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]
    (D : NonaffineData G X) (hsmall : Nat.card X < 25)
    (ell : ℕ) (hell : LeastProperIndex D.Simple ell)
    (horder : ell^2 < Nat.card D.Simple)
    (houter : SufficientOuterOrderBudget ell (Nat.card (Outer D.Simple))) :
    D.factorCount = 1 ∧ ArithmeticFunction.cardFactors (Nat.card (Outer D.Simple)) ≤ 3 := by
  have hell5 : 5 ≤ ell := nonabelianSimple_leastProperIndex_five_le
    (fun h => D.noncommutative (isMulCommutative_iff.mpr h)) hell.1
  have hdegree := primitiveSocle_power_le_degree hell5 horder (D.degreeForm hell)
  have hfive := (Nat.pow_le_pow_left hell5 D.factorCount).trans hdegree
  have hk : D.factorCount = 1 := by
    have hkpos := D.factorCount_pos
    by_contra hh
    have hpow := (Nat.pow_le_pow_right (by decide : 0 < 5)
      (show 2 ≤ D.factorCount by omega)).trans hfive
    norm_num at hpow
    omega
  have hellr := PrimitiveSocleLeastIndexDegreeComparison.least_index_le_degree D ell hell
  have hell32 : ell < 32 := by omega
  have hlog := Real.logb_lt_logb (by norm_num : (1 : ℝ) < 2)
    (by exact_mod_cast (show 0 < ell by omega) : (0 : ℝ) < ell)
    (by exact_mod_cast hell32 : (ell : ℝ) < 32)
  have h32 : Real.logb 2 (32 : ℝ) = 5 := by
    rw [show (32 : ℝ) = 2^5 by norm_num,Real.logb_pow,
      Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2)]
    norm_num
  rw [h32] at hlog
  have hout := houter.log_three_of_small (by omega)
  have hN : Nat.card (Outer D.Simple) < 2^(3+1) := by
    have hh : (Nat.card (Outer D.Simple) : ℝ) < 16 := by linarith only [hout,hlog]
    exact_mod_cast hh
  exact ⟨hk,SmallSharpOuterPairNumerics.cardFactors_le_of_lt_pow
    (Nat.card (Outer D.Simple)) 3 Nat.card_pos hN⟩

end SymmetricSubgroupAsymptotics.PrimitiveSocleDegreeBelowTwentyFiveOuterMultiplicity
