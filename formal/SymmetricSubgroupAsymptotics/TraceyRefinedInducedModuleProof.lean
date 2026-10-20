import SymmetricSubgroupAsymptotics.InducedMinimumCharacteristicBounds
import SymmetricSubgroupAsymptotics.InducedMinimumCoarseBound
import SymmetricSubgroupAsymptotics.InducedGenerationCoprimeSylow
import SymmetricSubgroupAsymptotics.TraceyElementaryLogBudget
import SymmetricSubgroupAsymptotics.TraceyRefinedAffineInput

/-! Unconditional refined induced-module capacities from actual Sylow
orbits, exact chain widths, Nakayama, and coprime semisimplicity. The least
actual uniform integer satisfies all five fields simultaneously. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics
namespace InducedMinimumUniformCapacity

variable {p : ℕ} [Fact p.Prime] {G V : Type} [Group G] [Finite G]
    [AddCommGroup V] [Module (ZMod p) V] [FiniteDimensional (ZMod p) V]
    (H : Subgroup G) (rho : Representation (ZMod p) H V)

theorem primeTo (q e : ℕ) (hq : q.Prime) (hqp : q≠p) (hdiv : q^e∣H.index) :
    (capacity H rho : ℝ)≤(Module.finrank (ZMod p) V : ℝ)*H.index/(q : ℝ)^e := by
  letI : Fact q.Prime := ⟨hq⟩
  let P : Sylow q G := Classical.choice inferInstance
  letI : Finite (DoubleCoset.Quotient (H : Set G) ((P : Subgroup G) : Set G)) :=
    Finite.of_injective (inducedDoubleCosetOrbitEquiv H (P : Subgroup G))
      (inducedDoubleCosetOrbitEquiv H (P : Subgroup G)).injective
  letI : Fintype (DoubleCoset.Quotient (H : Set G) ((P : Subgroup G) : Set G)) := Fintype.ofFinite _
  obtain ⟨B,hB,hprice⟩ := induced_coprime_sylow_uniform_with_price p q hqp H P rho e hdiv
  have hn : capacity H rho*q^e≤Module.finrank (ZMod p) V*H.index :=
    (Nat.mul_le_mul_right _ (le_of_uniform H rho hB)).trans hprice
  have hqR : (0 : ℝ)<q := by exact_mod_cast hq.pos
  apply (le_div_iff₀ (pow_pos hqR e)).mpr
  exact_mod_cast hn

theorem half (hs : 2≤H.index) :
    (capacity H rho : ℝ)≤(Module.finrank (ZMod p) V : ℝ)*H.index/2 := by
  by_cases hpdiv : p∣H.index
  · exact half_of_characteristic_dvd H rho hpdiv
  · obtain ⟨q,hq,hqdiv⟩ := Nat.exists_prime_and_dvd (by omega : H.index≠1)
    have hqp : q≠p := by rintro rfl; exact hpdiv hqdiv
    have h := primeTo H rho q 1 hq hqp (by simpa only [pow_one] using hqdiv)
    simp only [pow_one] at h
    apply h.trans
    exact div_le_div_of_nonneg_left (by positivity) (by norm_num)
      (by exact_mod_cast hq.two_le)

theorem primePower (q e : ℕ) (hq : q.Prime) (he : H.index=q^e) :
    (capacity H rho : ℝ)≤(Module.finrank (ZMod p) V : ℝ)*H.index*
      ((e*(q-1)).choose ((e*(q-1))/2) : ℝ)/(2 : ℝ)^(e*(q-1)) := by
  by_cases hqp : q=p
  · subst q
    exact characteristic_primePower H rho e he
  · have h := primeTo H rho q e hq hqp (by rw [he])
    have hq0 : (q : ℝ)≠0 := by exact_mod_cast hq.ne_zero
    rw [he,Nat.cast_pow,mul_div_cancel_right₀ _ (pow_ne_zero _ hq0)] at h
    have hm := mul_le_mul_of_nonneg_left (primeGrid_binomial_mass_one_le q e hq.pos)
      (show (0 : ℝ)≤Module.finrank (ZMod p) V by positivity)
    apply h.trans
    simpa only [mul_one,he,Nat.cast_pow,mul_div_assoc,mul_assoc] using hm

theorem logarithmic (hs : 2≤H.index) :
    (capacity H rho : ℝ)≤traceyInducedGeneratorCeiling (Module.finrank (ZMod p) V) H.index := by
  let s := H.index
  let a := Module.finrank (ZMod p) V
  let A : ℝ := (a : ℝ)*s
  let u : ℝ := (((p-1)*s.factorization p : ℕ) : ℝ)
  let L : ℝ := Real.logb 2 (s : ℝ)
  have hs0 : s≠0 := H.index_ne_zero_of_finite
  obtain ⟨v,hv,hpowers,hvchoice⟩ := TraceyElementaryLogBudget.exists_largest_other_power p s
  have hbudget := TraceyElementaryLogBudget.log_budget p s v
    (by have := (Fact.out : p.Prime).two_le; omega) hs0 hv hpowers
  have hu : u=((p : ℝ)-1)*(s.factorization p : ℝ) := by
    dsimp [u]
    rw [Nat.cast_mul,Nat.cast_sub (by have := (Fact.out : p.Prime).two_le; omega),Nat.cast_one]
  have hprimary : (capacity H rho : ℝ)^2*u≤2*A^2/3 := by
    by_cases hz : s.factorization p=0
    · simp only [u,hz,mul_zero,Nat.cast_zero]
      positivity
    · have he : 1 ≤ s.factorization p := by omega
      have hdiv : p^s.factorization p∣H.index :=
        ((Fact.out : p.Prime).pow_dvd_iff_le_factorization hs0).mpr le_rfl
      have h := primary H rho (s.factorization p) he hdiv
      have hup : (0 : ℝ)<u := by
        rw [hu]
        have hpR : (2 : ℝ)≤p := by exact_mod_cast (Fact.out : p.Prime).two_le
        have heR : (0 : ℝ)< s.factorization p := by exact_mod_cast he
        have hpmR : (0 : ℝ)<(p : ℝ)-1 := by linarith
        positivity
      have hden : 3*((p : ℝ)-1)*s.factorization p=3*u := by rw [hu]; ring
      rw [hden] at h
      change (capacity H rho : ℝ)≤A*Real.sqrt (2/(3*u)) at h
      have hsq := (sq_le_sq₀ (show (0 : ℝ)≤capacity H rho by positivity)
        (mul_nonneg (show 0≤A by dsimp [A]; positivity) (Real.sqrt_nonneg _))).mpr h
      rw [mul_pow,Real.sq_sqrt (by positivity : (0 : ℝ)≤2/(3*u))] at hsq
      apply (le_div_iff₀ hup).mp
      calc
        (capacity H rho : ℝ)^2≤A^2*(2/(3*u)) := hsq
        _ = (2*A^2/3)/u := by ring
  have hother : (capacity H rho : ℝ)*(v : ℝ)≤A := by
    rcases hvchoice with hv1 | ⟨q,hq,hqp,hvq⟩
    · simpa only [hv1,Nat.cast_one,mul_one] using coarse H rho
    · have hqprime := Nat.prime_of_mem_primeFactors hq
      have hdiv : q^s.factorization q∣H.index :=
        (hqprime.pow_dvd_iff_le_factorization hs0).mpr le_rfl
      have h := primeTo H rho q (s.factorization q) hqprime hqp hdiv
      have hqR : (0 : ℝ)<q := by exact_mod_cast hqprime.pos
      have hqpR : (0 : ℝ)<(q : ℝ)^s.factorization q := pow_pos hqR _
      have hmul := (le_div_iff₀ hqpR).mp h
      simpa only [hvq,Nat.cast_pow] using hmul
  have hLp : 0<L := Real.logb_pos (by norm_num) (by exact_mod_cast (by omega : 1<s))
  have h := TraceyElementaryLogBudget.cap_le_logarithmic
    (capacity H rho) A u v L (by positivity) (by dsimp [A]; positivity)
    (by positivity) hLp hbudget hprimary hother
  have hscale : 2*A/Real.sqrt L≤4*A/Real.sqrt L := by
    apply div_le_div_of_nonneg_right _ (Real.sqrt_nonneg L)
    have hA : 0≤A := by dsimp [A]; positivity
    linarith
  have hceil := Nat.le_ceil (4*A/Real.sqrt L)
  have hfinal := h.trans (hscale.trans hceil)
  simpa only [traceyInducedGeneratorCeiling,A,a,s,L,mul_assoc] using hfinal

end InducedMinimumUniformCapacity

/-- All five exact retained fields now follow from project and mathlib
proofs for the original arbitrary finite group and local representation. -/
theorem traceyRefinedInducedModuleInput_proved : TraceyRefinedInducedModuleInput := by
  intro p _ G _ _ H hs V _ _ _ rho
  refine ⟨InducedMinimumUniformCapacity.capacity H rho,?_,
    InducedMinimumUniformCapacity.uniform H rho⟩
  exact {
    half := InducedMinimumUniformCapacity.half H rho hs
    logarithmic := InducedMinimumUniformCapacity.logarithmic H rho hs
    primeTo := fun q e hq hqp _ hdiv => InducedMinimumUniformCapacity.primeTo H rho q e hq hqp hdiv
    primary := fun e he hdiv _ => InducedMinimumUniformCapacity.primary H rho e he hdiv
    primePower := fun q e hq _ he => InducedMinimumUniformCapacity.primePower H rho q e hq he }

end SymmetricSubgroupAsymptotics
