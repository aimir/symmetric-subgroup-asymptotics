import SymmetricSubgroupAsymptotics.TraceyRefinedInducedModuleProof

/-! The LEAST uniform capacity of an actual induced representation at
prime index costs at most its local dimension. In the defining prime,
the literal Sylow/Mackey decomposition has one orbit and one-coordinate
grid width1, before any binomial relaxation. In every other characteristic
the already proved prime-to-index theorem supplies the same result.
No dimension-only replacement action or local-capacity hypothesis occurs. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical BigOperators
namespace SymmetricSubgroupAsymptotics.InducedMinimumPrimeIndexCapacity

/-- A one-coordinate prime grid has exactly one point at its middle rank. -/
theorem primeGrid_one_width (q : ℕ) (hq : 0 < q) : primeGridMiddleWidth q 1 = 1 := by
  have hlt : (q-1)/2 < q := by
    have hh := Nat.div_le_self (q-1) 2
    omega
  let z : PrimeCosetGrid q 1 := (⟨(q-1)/2,hlt⟩,())
  have hfilter : Finset.univ.filter (fun x : PrimeCosetGrid q 1 =>
      primeGridRank q 1 x = (1*(q-1))/2) = {z} := by
    ext y
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_singleton,
      primeGridRank,Nat.add_zero,Nat.one_mul]
    constructor
    · intro hy
      apply Prod.ext
      · exact Fin.ext hy
      · change y.2 = ()
        cases y.2
        rfl
    · intro hy
      exact congrArg (fun x : PrimeCosetGrid q 1 => x.1.val) hy
  unfold primeGridMiddleWidth
  rw [hfilter,Finset.card_singleton]

variable {p : ℕ} [Fact p.Prime] {G V : Type} [Group G] [Finite G]
    [AddCommGroup V] [Module (ZMod p) V] [FiniteDimensional (ZMod p) V]
    (H : Subgroup G) (rho : Representation (ZMod p) H V)

theorem characteristic_prime_index (hindex : H.index = p) :
    InducedMinimumUniformCapacity.capacity H rho ≤ Module.finrank (ZMod p) V := by
  have hindex' : H.index = p^1 := by simpa only [pow_one] using hindex
  let P : Sylow p G := Classical.choice inferInstance
  letI : Finite (DoubleCoset.Quotient (H : Set G) ((P : Subgroup G) : Set G)) :=
    Finite.of_injective (inducedDoubleCosetOrbitEquiv H (P : Subgroup G))
      (inducedDoubleCosetOrbitEquiv H (P : Subgroup G)).injective
  letI : Fintype (DoubleCoset.Quotient (H : Set G) ((P : Subgroup G) : Set G)) := Fintype.ofFinite _
  obtain ⟨j,hj,hval,hs⟩ := inducedMackeySylow_indices H p P
  have hje (q) : j q = 1 := by
    apply Nat.le_antisymm
    · apply (Nat.pow_le_pow_iff_right (Fact.out : p.Prime).one_lt).mp
      rw [←hindex',←hs]
      exact Finset.single_le_sum (f := fun q => p^j q)
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ q)
    · have h := hval q
      simpa only [hindex',Nat.factorization_pow_self (Fact.out : p.Prime)] using h
  have hcard : Fintype.card (DoubleCoset.Quotient (H : Set G) ((P : Subgroup G) : Set G)) = 1 := by
    have heq : Fintype.card (DoubleCoset.Quotient (H : Set G) ((P : Subgroup G) : Set G))*p^1 = 1*p^1 := by
      simpa only [hje,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,hindex',one_mul] using hs
    exact Nat.eq_of_mul_eq_mul_right (pow_pos (Fact.out : p.Prime).pos _) heq
  have hn := InducedMinimumUniformCapacity.le_of_uniform H rho
    (induced_sylow_middle_uniform H P rho j hj)
  simpa only [hje,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,hcard,Nat.one_mul,
    primeGrid_one_width p (Fact.out : p.Prime).pos,Nat.mul_one,Nat.cast_one,one_mul] using hn

theorem prime_index (q : ℕ) (hq : q.Prime) (hindex : H.index = q) :
    InducedMinimumUniformCapacity.capacity H rho ≤ Module.finrank (ZMod p) V := by
  by_cases hqp : q = p
  · exact characteristic_prime_index H rho (hindex.trans hqp)
  · have hb := InducedMinimumUniformCapacity.primeTo H rho q 1 hq hqp
      (show q^1 ∣ H.index by simpa only [hindex,pow_one] using (dvd_refl q))
    rw [hindex,pow_one] at hb
    have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne_zero
    rw [mul_div_cancel_right₀ _ hq0] at hb
    exact_mod_cast hb

end SymmetricSubgroupAsymptotics.InducedMinimumPrimeIndexCapacity
