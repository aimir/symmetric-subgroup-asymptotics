import SymmetricSubgroupAsymptotics.GoodSylowPrimeOrderOrdinaryGenerators
import SymmetricSubgroupAsymptotics.CFSGTwoGenerationBasic
import SymmetricSubgroupAsymptotics.PrimitiveSocleOuterMultiplicityDegreeBounds
import SymmetricSubgroupAsymptotics.FiniteModelPrimitiveOrdinaryBudget

/-! Actual root/Sylow data imply a uniform simple quadratic-log rank cost;
the whole primitive socle then pays all factors without smaller-action
induction. These are internal data consumers, not new endpoint callbacks. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.PrimitiveSimplePolylogRankTools
open PrimitiveSocleRawStructure

private theorem log_ge_one (ell : ℕ) (hell : 2≤ell) : 1≤Real.logb 2 (ell : ℝ) := by
  have hh := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ)<2)
    (by norm_num : (0 : ℝ)<2) (by exact_mod_cast hell : (2 : ℝ)≤ell)
  simpa only [Real.logb_self_eq_one (by norm_num : (1 : ℝ)<2)] using hh

theorem field_dimension_le_log (q : CFSG.PrimePower) (r ell : ℕ)
    (hfield : q.order^r≤ell) :
    ((q.exponent*r : ℕ) : ℝ)≤Real.logb 2 (ell : ℝ) := by
  have hp : 2^(q.exponent*r)≤ell := by
    calc
      _=(2^q.exponent)^r := pow_mul 2 q.exponent r
      _≤q.order^r := Nat.pow_le_pow_left (Nat.pow_le_pow_left q.prime_isPrime.two_le q.exponent) r
      _≤ell := hfield
  have hh := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ)<2)
    (by positivity : (0 : ℝ)<(2 : ℝ)^(q.exponent*r))
    (by exact_mod_cast hp : (2 : ℝ)^(q.exponent*r)≤ell)
  simpa only [Real.logb_pow,Real.logb_self_eq_one (by norm_num : (1 : ℝ)<2),mul_one] using hh

theorem rank_le_of_pair {T : Type} [Group T] [Finite T]
    (hp : CFSGGeneration.TwoGenerated T) (ell : ℕ) (hell : 2≤ell) :
    (MarkedC4.genRank T : ℝ)≤12*(Real.logb 2 (ell : ℝ))^2+1 := by
  obtain ⟨S,hS,hcard⟩ := hp
  have hr : (MarkedC4.genRank T : ℝ)≤2 := by exact_mod_cast (MarkedC4.genRank_le hS).trans hcard
  have hl := log_ge_one ell hell
  nlinarith only [hr,hl,sq_nonneg (Real.logb 2 (ell : ℝ)-1)]

theorem rank_le_of_roots {T : Type} [Group T] [Finite T]
    (q : CFSG.PrimePower) (r ell : ℕ) (hr : 0<r)
    (S : Finset T) (hS : Subgroup.closure (S : Set T)=⊤)
    (hcard : S.card≤4*(q.exponent*r)) (hfield : q.order^r≤ell) :
    (MarkedC4.genRank T : ℝ)≤12*(Real.logb 2 (ell : ℝ))^2+1 := by
  have hd := field_dimension_le_log q r ell hfield
  have her : (1 : ℝ)≤((q.exponent*r : ℕ) : ℝ) := by
    exact_mod_cast (Nat.succ_le_iff.mpr (Nat.mul_pos q.exponent_pos hr))
  have hrank : (MarkedC4.genRank T : ℝ)≤4*((q.exponent*r : ℕ) : ℝ) := by
    exact_mod_cast (MarkedC4.genRank_le hS).trans hcard
  have hl : 1≤Real.logb 2 (ell : ℝ) := her.trans hd
  nlinarith only [hrank,hd,hl,sq_nonneg (Real.logb 2 (ell : ℝ)-1)]

theorem rank_le_of_sylow {A T : Type} [Group A] [Finite A] [Group T] [Finite T]
    (q : CFSG.PrimePower) (r a ell : ℕ) (ha : a≤12*r^2)
    (hgood : CFSGReduction.GoodSylowPrime A q.prime) (P : Sylow q.prime A)
    (hP : Nat.card P∣q.prime^(q.exponent*a))
    (f : A →* T) (hf : Function.Surjective f) (hfield : q.order^r≤ell) :
    (MarkedC4.genRank T : ℝ)≤12*(Real.logb 2 (ell : ℝ))^2+1 := by
  have hs := GoodSylowPrimeOrderOrdinaryGenerators.genRank_le_of_surjective_prime_power
    q.prime (q.exponent*a) hgood P hP f hf
  have hcount : q.exponent*a≤12*(q.exponent*r)^2 := by
    calc
      q.exponent*a≤q.exponent*(12*r^2) := Nat.mul_le_mul_left _ ha
      _=12*(q.exponent*r^2) := by ring
      _≤12*(q.exponent^2*r^2) := Nat.mul_le_mul_left _
        (Nat.mul_le_mul_right _ (Nat.le_self_pow (by decide : 2≠0) q.exponent))
      _=12*(q.exponent*r)^2 := by rw [mul_pow]
  have hrank : (MarkedC4.genRank T : ℝ)≤12*((q.exponent*r : ℕ) : ℝ)^2+1 := by
    exact_mod_cast hs.trans (Nat.add_le_add_right hcount 1)
  have hd := field_dimension_le_log q r ell hfield
  have hsquare := mul_self_le_mul_self (Nat.cast_nonneg (q.exponent*r)) hd
  nlinarith only [hrank,hsquare]

theorem primitive_rank_le_of_simple_packet
    {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]
    [FaithfulSMul G X] [Nontrivial X] [MulAction.IsPreprimitive G X]
    (D : NonaffineData G X) (ell : ℕ) (hell : LeastProperIndex D.Simple ell)
    (horder : ell^2<Nat.card D.Simple)
    (houter : SufficientOuterOrderBudget ell (Nat.card (Outer D.Simple)))
    (hsimple : (MarkedC4.genRank D.Simple : ℝ)≤12*(Real.logb 2 (ell : ℝ))^2+1) :
    (MarkedC4.genRank G : ℝ)≤25*(Real.logb 2 (Nat.card X : ℝ))^2+
      4*Real.logb 2 (Nat.card X : ℝ)+2 := by
  have hell2 : 2≤ell := by
    obtain ⟨H,hH,he⟩ := hell.1
    have hh := H.one_lt_index_of_ne_top hH
    omega
  have hidx := PrimitiveSocleLeastIndexDegreeComparison.least_index_le_degree D ell hell
  have hl := log_ge_one ell hell2
  have hL := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ)<2)
    (by exact_mod_cast (show 0<ell by omega) : (0 : ℝ)<(ell : ℝ))
    (by exact_mod_cast hidx : (ell : ℝ)≤(Nat.card X : ℝ))
  have hsq := mul_self_le_mul_self (by linarith : 0≤Real.logb 2 (ell : ℝ)) hL
  have hcost := PrimitiveSocleOuterMultiplicityDegreeBounds.multiplicity_le_quadratic_log
    D ell hell horder houter
  have hbase := PrimitiveSocleIsotypicOrdinaryCompression.genRank_le_twice_simple_add_quotient D
  have hquot := PrimitiveSocleStrictOuterOrdinaryRecurrence.quotient_genRank_le_outer_multiplicity D
  have hr : (MarkedC4.genRank G : ℝ)≤2*(MarkedC4.genRank D.Simple : ℝ)+
      ((D.factorCount*ArithmeticFunction.cardFactors (Nat.card (Outer D.Simple))+
        ArithmeticFunction.cardFactors D.factorCount.factorial : ℕ) : ℝ) := by
    exact_mod_cast hbase.trans (Nat.add_le_add_left hquot _)
  nlinarith only [hsimple,hsq,hcost,hr]

end SymmetricSubgroupAsymptotics.PrimitiveSimplePolylogRankTools
