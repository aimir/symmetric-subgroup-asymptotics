import SymmetricSubgroupAsymptotics.ActualWreathCharacteristicChiefProfile
import SymmetricSubgroupAsymptotics.FiniteGroupPrimeMultiplicityGenerators

/-! A joint defining-prime/total-prime budget along the SAME actual
ordinary chief trace. A nonabelian layer is paid by the ordinary rank of
its actual selected internal simple factor, detected injectively in one
original coordinate. No simple two-generation, solvability, CFSG, or
published permutation-generator input is used. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.ActualWreathChiefPrimeMultiplicityBudget
open PermutationalWreathProduct ActualWreathCharacteristicChiefProfile
open FiniteGroupPrimeMultiplicityGenerators

/-- The defining-prime excess and every other charge consume one common
ACTUAL order; the central binomial coefficient is always at least one. -/
def binaryOrderCost (M e : ℕ) : ℕ :=
  M.factorization 2 * (e.choose (e/2) - 1) + ArithmeticFunction.cardFactors M

theorem binaryOrderCost_mul {M N : ℕ} (hM : M ≠ 0) (hN : N ≠ 0) (e : ℕ) :
    binaryOrderCost (M*N) e = binaryOrderCost M e + binaryOrderCost N e := by
  simp only [binaryOrderCost,Nat.factorization_mul hM hN,Finsupp.add_apply,
    ArithmeticFunction.cardFactors_mul hM hN]
  ring

theorem binaryOrderCost_mono_of_dvd {M N : ℕ} (hM : M ≠ 0) (hN : N ≠ 0)
    (hMN : M ∣ N) (e : ℕ) : binaryOrderCost M e ≤ binaryOrderCost N e := by
  have hv := (Nat.factorization_le_iff_dvd hM hN).mpr hMN
  exact Nat.add_le_add (Nat.mul_le_mul_right _ (hv 2))
    (cardFactors_mono_of_dvd hM hN hMN)

theorem elementary_capacity_le_binaryOrderCost {t : ℕ} (c : ElementaryCharge t)
    (e : ℕ) (ht : t = 2^e) : c.capacity ≤ binaryOrderCost (c.p^c.dimension) e := by
  have htR : (t : ℝ) = (2 : ℝ)^e := by exact_mod_cast ht
  have hpow : (2 : ℝ)^e ≠ 0 := by positivity
  have hchoose : 1 ≤ e.choose (e/2) := Nat.choose_pos (Nat.div_le_self e 2)
  have hOmega : ArithmeticFunction.cardFactors (c.p^c.dimension) = c.dimension :=
    ArithmeticFunction.cardFactors_apply_prime_pow c.prime
  by_cases hp : c.p = 2
  · have hv : (c.p^c.dimension).factorization 2 = c.dimension := by
      rw [hp,Nat.prime_two.factorization_pow]
      simp only [Finsupp.single_eq_same]
    have hh := c.primePower 2 e Nat.prime_two ht
    simp only [show 2-1 = (1 : ℕ) by omega,mul_one] at hh
    rw [htR] at hh
    have hc : c.capacity ≤ c.dimension * e.choose (e/2) := by
      have hcancel (a b : ℝ) : a*(2 : ℝ)^e*b/(2 : ℝ)^e = a*b := by
        rw [mul_right_comm,mul_div_cancel_right₀ _ hpow]
      rw [hcancel] at hh
      exact_mod_cast hh
    have heq : binaryOrderCost (c.p^c.dimension) e = c.dimension*e.choose (e/2) := by
      simp only [binaryOrderCost,hv,hOmega]
      have he : e.choose (e/2) - 1 + 1 = e.choose (e/2) := Nat.sub_add_cancel hchoose
      nlinarith
    exact hc.trans_eq heq.symm
  · have hv : (c.p^c.dimension).factorization 2 = 0 := by
      rw [c.prime.factorization_pow]
      exact Finsupp.single_eq_of_ne (Ne.symm hp)
    have hh := c.primeTo 2 e Nat.prime_two (Ne.symm hp) (by rw [ht])
    norm_num only [Nat.cast_ofNat] at hh
    rw [htR,mul_div_cancel_right₀ _ hpow] at hh
    have hc : c.capacity ≤ c.dimension := by exact_mod_cast hh
    simpa only [binaryOrderCost,hv,zero_mul,zero_add,hOmega] using hc

section Factor
variable {A D D' Q I : Type} [Group A] [Group D] [Finite D]
    [Group D'] [Group Q] [MulAction Q I]

theorem factor_genRank_le_local_cardFactors
    (rho : A →* PermutationalWreathProduct D Q I) (phi : D →* D')
    (hrho : Function.Injective rho)
    (C : SemisimpleNormalChart (Compression.kernel rho phi)) (j : C.ι) :
    MarkedC4.genRank (C.factor j) ≤ ArithmeticFunction.cardFactors (Nat.card phi.ker) := by
  classical
  obtain ⟨i,hfi⟩ := SemisimpleChartCoordinateFactorEmbedding.factor_has_injective_coordinate
    (Compression.kernel rho phi) C (fun _ => phi.ker)
    (Compression.kernelCoordinate rho phi)
    (Compression.kernelCoordinate_joint_injective rho phi hrho) j
  have hd := Subgroup.card_dvd_of_injective _ hfi
  have hfinite : Finite (C.factor j) := Finite.of_injective _ hfi
  letI : Finite (C.factor j) := hfinite
  exact (genRank_le_cardFactors (C.factor j)).trans
    (cardFactors_mono_of_dvd (Nat.card_pos (α := C.factor j)).ne'
      (Nat.card_pos (α := phi.ker)).ne' hd)

end Factor

section Chief
variable {Q I : Type} [Group Q] [Fintype I] [Nonempty I]
    [MulAction Q I] [FaithfulSMul Q I]

theorem cost_le_binaryOrderCost {i : I} {S : ActualWreathCompressionState Q I} {n : ℕ}
    (h : ActualWreathOrdinaryChiefRecurrence.ChiefCost i S n)
    (hI : 2 ≤ Fintype.card I) (e : ℕ) (ht : Fintype.card I = 2^e) :
    n ≤ binaryOrderCost (Nat.card S.D) e := by
  induction h with
  | terminal S hD => exact Nat.zero_le _
  | vanishing S D' phi hphi hmin hz n next ih =>
      exact ih.trans (binaryOrderCost_mono_of_dvd
        (Nat.card_pos (α := D')).ne' (Nat.card_pos (α := S.D)).ne'
        (Subgroup.card_dvd_of_surjective phi hphi) e)
  | elementary S D' phi hphi hmin C n next ih =>
      have hc := elementary_capacity_le_binaryOrderCost (actualCharge S phi C i hI) e ht
      change ActualWreathElementaryOrdinaryStep.layerCapacity S phi C i ≤
        binaryOrderCost (C.p ^ Module.finrank (ZMod C.p) C.V) e at hc
      rw [←ActualWreathChiefHalfOrderBudget.elementary_kernel_card phi C] at hc
      change n ≤ binaryOrderCost (Nat.card D') e at ih
      have hh := Nat.add_le_add hc ih
      rw [←binaryOrderCost_mul (Nat.card_pos (α := phi.ker)).ne'
        (Nat.card_pos (α := D')).ne' e,
        ActualWreathChiefHalfOrderBudget.card_kernel_mul_card_of_surjective phi hphi] at hh
      exact hh
  | nonabelian S D' phi hphi hmin hnc hne C j n next ih =>
      have hc := factor_genRank_le_local_cardFactors S.rho phi S.rho_injective C j
      have hc' : MarkedC4.genRank (C.factor j) ≤ binaryOrderCost (Nat.card phi.ker) e :=
        hc.trans (Nat.le_add_left _ _)
      change n ≤ binaryOrderCost (Nat.card D') e at ih
      have hh := Nat.add_le_add hc' ih
      rw [←binaryOrderCost_mul (Nat.card_pos (α := phi.ker)).ne'
        (Nat.card_pos (α := D')).ne' e,
        ActualWreathChiefHalfOrderBudget.card_kernel_mul_card_of_surjective phi hphi] at hh
      exact hh

theorem exists_binaryOrderCost_bound (S : ActualWreathCompressionState Q I)
    (i : I) (hI : 2 ≤ Fintype.card I) (e : ℕ) (ht : Fintype.card I = 2^e) :
    ∃ n : ℕ, ActualWreathOrdinaryChiefRecurrence.ChiefCost i S n ∧
      n ≤ binaryOrderCost (Nat.card S.D) e ∧
      MarkedC4.genRank S.A ≤ n + MarkedC4.genRank Q := by
  obtain ⟨n,hn⟩ := ActualWreathOrdinaryChiefRecurrence.exists_chiefCost i S
  exact ⟨n,hn,cost_le_binaryOrderCost hn hI e ht,
    ActualWreathOrdinaryChiefRecurrence.genRank_le_cost_add_top hn⟩
end Chief
end SymmetricSubgroupAsymptotics.ActualWreathChiefPrimeMultiplicityBudget
