import SymmetricSubgroupAsymptotics.InducedMinimumPrimeIndexCapacity

/-! At a literal induction index m divisible by prime q but smaller than
q squared, every defining-q Mackey Sylow orbit has length exactly q.
Its actual one-coordinate prime grid has width one. All other defining
characteristics use the already proved prime-to-q bound. This is stronger
than replacing the q-grid by a binary central-binomial relaxation. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical BigOperators
namespace SymmetricSubgroupAsymptotics.InducedMinimumSmallPrimeMultipleCapacity

variable {p : ℕ} [Fact p.Prime] {G V : Type} [Group G] [Finite G]
    [AddCommGroup V] [Module (ZMod p) V] [FiniteDimensional (ZMod p) V]
    (H : Subgroup G) (rho : Representation (ZMod p) H V)

theorem characteristic_small_multiple (hdiv : p ∣ H.index) (hsmall : H.index < p^2) :
    (InducedMinimumUniformCapacity.capacity H rho : ℝ) ≤
      (Module.finrank (ZMod p) V : ℝ)*H.index/(p : ℝ) := by
  let P : Sylow p G := Classical.choice inferInstance
  letI : Finite (DoubleCoset.Quotient (H : Set G) ((P : Subgroup G) : Set G)) :=
    Finite.of_injective (inducedDoubleCosetOrbitEquiv H (P : Subgroup G))
      (inducedDoubleCosetOrbitEquiv H (P : Subgroup G)).injective
  letI : Fintype (DoubleCoset.Quotient (H : Set G) ((P : Subgroup G) : Set G)) := Fintype.ofFinite _
  obtain ⟨j,hj,hval,hs⟩ := inducedMackeySylow_indices H p P
  have hval1 : 1 ≤ H.index.factorization p :=
    ((Fact.out : p.Prime).pow_dvd_iff_le_factorization H.index_ne_zero_of_finite).mp
      (by simpa only [pow_one] using hdiv)
  have hje (z) : j z = 1 := by
    have hlo : 1 ≤ j z := hval1.trans (hval z)
    have hpow : p^j z ≤ H.index := by
      rw [←hs]
      exact Finset.single_le_sum (f := fun z => p^j z)
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ z)
    have hlt : j z < 2 := (Nat.pow_lt_pow_iff_right (Fact.out : p.Prime).one_lt).mp
      (hpow.trans_lt hsmall)
    omega
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hh := InducedMinimumUniformCapacity.le_of_sylow_middle H rho P j hj hs (1/(p : ℝ)) (by
    intro z
    rw [hje,InducedMinimumPrimeIndexCapacity.primeGrid_one_width p (Fact.out : p.Prime).pos,
      pow_one,Nat.cast_one]
    exact le_of_eq (by field_simp [hp0]))
  simpa only [mul_one_div] using hh

theorem small_multiple_prime (q : ℕ) (hq : q.Prime)
    (hdiv : q ∣ H.index) (hsmall : H.index < q^2) :
    (InducedMinimumUniformCapacity.capacity H rho : ℝ) ≤
      (Module.finrank (ZMod p) V : ℝ)*H.index/(q : ℝ) := by
  by_cases hqp : q = p
  · subst q
    exact characteristic_small_multiple H rho hdiv hsmall
  · have hh := InducedMinimumUniformCapacity.primeTo H rho q 1 hq hqp
      (by simpa only [pow_one] using hdiv)
    simpa only [pow_one] using hh

theorem six_index (hindex : H.index = 6) :
    InducedMinimumUniformCapacity.capacity H rho ≤ 2*Module.finrank (ZMod p) V := by
  have hh := small_multiple_prime H rho 3 Nat.prime_three
    (by rw [hindex]; decide) (by rw [hindex]; decide)
  rw [hindex] at hh
  have hbound : (InducedMinimumUniformCapacity.capacity H rho : ℝ) ≤
      2*(Module.finrank (ZMod p) V : ℝ) := by linarith only [hh]
  exact_mod_cast hbound

end SymmetricSubgroupAsymptotics.InducedMinimumSmallPrimeMultipleCapacity
