import SymmetricSubgroupAsymptotics.PrimitiveSocleOneFactorOrdinaryRecurrence
import SymmetricSubgroupAsymptotics.PrimitiveSocleLeastIndexDegreeComparison
import SymmetricSubgroupAsymptotics.FiniteModelPrimitiveOrdinaryBudget
import SymmetricSubgroupAsymptotics.TraceyCoarseCeilingMonotonicity

/-! A classification-free primitive comparator. The hypotheses are literal
properties of the SAME selected simple factor. No order formula, index-square
bound, smaller-action induction or classification callback is used. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.PrimitiveElevenHeadTrivialOuterOrdinary
open PrimitiveSocleRawStructure CFSGReduction

private def charge (k : ℕ) : ℕ := k^2+22

private theorem charge_step (k : ℕ) : charge (k+1) ≤ 3*charge k := by
  dsimp only [charge]
  nlinarith

private theorem polynomial_lt_power (k : ℕ) (hk : 3 ≤ k) :
    3*k*(charge k)^2 < 49^k := by
  induction k, hk using Nat.le_induction with
  | base => decide
  | succ k hk ih =>
    have hstep := charge_step k
    have hkstep : k+1 ≤ 2*k := by omega
    have hsquare := Nat.pow_le_pow_left hstep 2
    calc
      3*(k+1)*(charge (k+1))^2 ≤ 3*(2*k)*(3*charge k)^2 :=
        Nat.mul_le_mul (Nat.mul_le_mul_left 3 hkstep) hsquare
      _ = 18*(3*k*(charge k)^2) := by ring
      _ < 18*49^k := Nat.mul_lt_mul_of_pos_left ih (by decide)
      _ ≤ 49*49^k := Nat.mul_le_mul_right _ (by decide)
      _ = 49^(k+1) := by rw [pow_succ]; ring

/-- An integer certificate, valid uniformly from three factors onward. -/
theorem charge_le_ceiling_power (k : ℕ) (hk : 3 ≤ k) :
    k^2+22 ≤ traceyPermutationGeneratorCeiling (7^k) := by
  have hp := polynomial_lt_power k hk
  have hpow : (7^k)^1 ≤ 2^(3*k) := by
    simpa only [pow_one, pow_mul] using
      (Nat.pow_le_pow_left (by decide : 7 ≤ 2^3) k)
  have hsq : (7^k)^2 = 49^k := by
    calc
      (7^k)^2 = 7^(k*2) := (pow_mul 7 k 2).symm
      _ = 7^(2*k) := by rw [Nat.mul_comm k 2]
      _ = 49^k := by rw [pow_mul]; norm_num
  have hsmall : (charge k-1)^2 ≤ (charge k)^2 :=
    Nat.pow_le_pow_left (Nat.sub_le _ _) 2
  have hcert : (charge k-1)^2*(3*k) < 1*(7^k)^2 := by
    have hh := (Nat.mul_le_mul_right (3*k) hsmall).trans_lt
      (show (charge k)^2*(3*k) < 49^k by simpa only [mul_comm] using hp)
    simpa only [one_mul, hsq] using hh
  exact IntegerLogSquareRootCeilingCertificate.le_ceil_of_square
    (7^k) 1 (3*k) (charge k)
    (by
      have hh : 7^1 ≤ 7^k := Nat.pow_le_pow_right (by decide) (by omega)
      norm_num at hh ⊢
      omega)
    (by decide) (by dsimp only [charge]; omega) hpow hcert

theorem eleven_le_ceiling {n : ℕ} (hn : 27 ≤ n) :
    11 ≤ traceyPermutationGeneratorCeiling n := by
  have h27 : 11 ≤ traceyPermutationGeneratorCeiling 27 :=
    IntegerLogSquareRootCeilingCertificate.le_ceil_of_square 27 1 5 11
      (by decide) (by decide) (by decide) (by decide) (by decide)
  exact h27.trans (TraceyCoarseCeilingMonotonicity.ceiling_mono (by decide) hn)

theorem twentyThree_le_ceiling {n : ℕ} (hn : 60 ≤ n) :
    23 ≤ traceyPermutationGeneratorCeiling n := by
  have h60 : 23 ≤ traceyPermutationGeneratorCeiling 60 :=
    IntegerLogSquareRootCeilingCertificate.le_ceil_of_square 60 1 6 23
      (by decide) (by decide) (by decide) (by decide) (by decide)
  exact h60.trans (TraceyCoarseCeilingMonotonicity.ceiling_mono (by decide) hn)

variable {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]
    [FaithfulSMul G X] [Nontrivial X] [MulAction.IsPreprimitive G X]
    (D : NonaffineData G X)

private theorem seven_power_le_degree (ell : ℕ)
    (hell : LeastProperIndex D.Simple ell) (hlarge : 27 ≤ ell) :
    7^D.factorCount ≤ Nat.card X := by
  have ho := NonabelianSimpleOrderAtLeastSixty.sixty_le_card D.Simple D.noncommutative
  have hform : PrimitiveSocleDegreeForm 7 (Nat.card D.Simple)
      D.factorCount (Nat.card X) := by
    rcases D.degreeForm hell with ⟨a,ha,he⟩ | ⟨a,ha,he⟩
    · exact Or.inl ⟨a,by omega,he⟩
    · exact Or.inr ⟨a,ha,he⟩
  exact primitiveSocle_power_le_degree (by decide) (by omega) hform

private theorem sixty_le_degree_of_two (ell : ℕ)
    (hell : LeastProperIndex D.Simple ell) (hlarge : 27 ≤ ell)
    (hk : D.factorCount=2) : 60 ≤ Nat.card X := by
  have ho := NonabelianSimpleOrderAtLeastSixty.sixty_le_card D.Simple D.noncommutative
  rcases D.degreeForm hell with ⟨a,ha,he⟩ | ⟨a,ha,he⟩
  · rw [he, hk]
    have hh := Nat.pow_le_pow_left (show 27 ≤ a by omega) 2
    norm_num at hh
    omega
  · have ha1 : 1 ≤ a := by rw [hk] at ha; omega
    have hp : Nat.card D.Simple ≤ (Nat.card D.Simple)^a := by
      simpa only [pow_one] using Nat.pow_le_pow_right
        (Nat.card_pos (α := D.Simple)) ha1
    exact ho.trans (hp.trans_eq he.symm)

/-- The common simple factor is retained throughout. The public raw-Monster
instantiation discharges these three structural facts internally. -/
theorem genRank_le_ceiling (hhead : MarkedC4.genRank D.Simple ≤ 11)
    (houter : Nat.card (Outer D.Simple)=1) (ell : ℕ)
    (hell : LeastProperIndex D.Simple ell) (hlarge : 27 ≤ ell) :
    MarkedC4.genRank G ≤ traceyPermutationGeneratorCeiling (Nat.card X) := by
  by_cases hk : D.factorCount=1
  · have h := PrimitiveSocleOneFactorOrdinaryRecurrence.genRank_le_simple_add_outer_multiplicity D hk
    rw [houter, ArithmeticFunction.cardFactors_one, add_zero] at h
    exact (h.trans hhead).trans (eleven_le_ceiling
      (hlarge.trans (PrimitiveSocleLeastIndexDegreeComparison.least_index_le_degree D ell hell)))
  · have hc := PrimitiveSocleIsotypicOrdinaryCompression.genRank_le_twice_simple_add_quotient D
    have hq := PrimitiveSocleStrictOuterOrdinaryRecurrence.quotient_genRank_le_outer_multiplicity D
    simp only [houter, ArithmeticFunction.cardFactors_one, mul_zero, zero_add] at hq
    have htotal : MarkedC4.genRank G ≤ 22+
        ArithmeticFunction.cardFactors D.factorCount.factorial := by
      have hh := hc.trans (Nat.add_le_add_left hq _)
      have hb := Nat.mul_le_mul_left 2 hhead
      omega
    by_cases hk2 : D.factorCount=2
    · have hf : ArithmeticFunction.cardFactors D.factorCount.factorial=1 := by
        rw [hk2]
        decide +kernel
      rw [hf] at htotal
      exact htotal.trans (twentyThree_le_ceiling (sixty_le_degree_of_two D ell hell hlarge hk2))
    · have hthree : 3 ≤ D.factorCount := by have hp := D.factorCount_pos; omega
      have hf := FiniteModelPrimitiveOrdinaryBudget.factorial_cardFactors_le_square D.factorCount
      have hpower := seven_power_le_degree D ell hell hlarge
      have hm := TraceyCoarseCeilingMonotonicity.ceiling_mono
        (show 2 ≤ 7^D.factorCount by
          have hh : 7^1 ≤ 7^D.factorCount := Nat.pow_le_pow_right (by decide : 0 < 7)
            (show 1 ≤ D.factorCount by omega)
          norm_num at hh ⊢
          omega) hpower
      exact (show MarkedC4.genRank G ≤ D.factorCount^2+22 by omega).trans
        ((charge_le_ceiling_power _ hthree).trans hm)

end SymmetricSubgroupAsymptotics.PrimitiveElevenHeadTrivialOuterOrdinary
