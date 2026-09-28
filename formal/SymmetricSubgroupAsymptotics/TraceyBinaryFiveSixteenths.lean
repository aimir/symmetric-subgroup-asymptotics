import SymmetricSubgroupAsymptotics.TraceyBinaryFormulaInput

/-!
# The sharp binary fixed-section budget

The exact Tracey formula proves the `5/16` bound in every degree except the
nonsoluble `3 * 2^a` frontier.  The one additional visible literature input
below is precisely the head bound supplied there by Tracey's minimally
transitive orbit theorem (Corollary 3.12, together with the preceding
`PSL₂` construction excluding the Mersenne prime three).
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
attribute [local instance] Fintype.ofFinite

namespace SymmetricSubgroupAsymptotics

/-- The sole exceptional consequence imported from Tracey's minimally
transitive `3 * 2^a` orbit theorem.  It is stated on literal heads of
subrepresentations; passage to arbitrary quotient sections is proved below. -/
def TraceyBinaryExceptionalThreeInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G]
    (X : Type) [Finite X] [MulAction G X] [FaithfulSMul G X]
      [MulAction.IsPretransitive G X]
    (M : Subrepresentation
      (permutationFunctionRepresentation (ZMod 2) G X)),
    24 ≤ Nat.card X → ordCompl[2] (Nat.card X) = 3 →
      16 * Module.finrank (ZMod 2) (M.toRepresentation.IntertwiningMap
        (Representation.trivial (ZMod 2) G (ZMod 2))) ≤ 5 * Nat.card X

/-- From exponent five onward the middle binary coefficient has density at
most `5/16`. -/
theorem binary_middle_le_five_sixteenths (a : ℕ) (ha : 5 ≤ a) :
    16 * a.choose (a / 2) ≤ 5 * 2 ^ a := by
  induction a, ha using Nat.le_induction with
  | base => decide
  | succ a ha ih =>
      calc
        16 * (a + 1).choose ((a + 1) / 2) ≤
            16 * (2 * a.choose (a / 2)) :=
          Nat.mul_le_mul_left 16 (binary_middle_succ_le_twice a)
        _ = 2 * (16 * a.choose (a / 2)) := by ring
        _ ≤ 2 * (5 * 2 ^ a) := Nat.mul_le_mul_left 2 ih
        _ = 5 * 2 ^ (a + 1) := by rw [pow_succ]; ring

/-- An odd integer other than one or three has a prime-power divisor at
least five. -/
theorem largestPrimePower_odd_ge_five (n : ℕ) (hn : n ≠ 0)
    (hodd : ¬2 ∣ n) (h1 : n ≠ 1) (h3 : n ≠ 3) :
    5 ≤ largestPrimePower n := by
  by_contra h
  have hl : largestPrimePower n ≤ 4 := by omega
  have hd : n ∣ 3 := (Nat.factorization_le_iff_dvd hn (by decide)).mp (by
    intro p
    by_cases hp0 : n.factorization p = 0
    · simp [hp0]
    have hprime : p.Prime := Nat.prime_of_mem_primeFactors
      (show p ∈ n.primeFactors from Finsupp.mem_support_iff.mpr hp0)
    have hpv : p ^ n.factorization p ≤ 4 :=
      (primePower_le_largestPrimePower n p).trans hl
    have hple : p ≤ 4 :=
      (Nat.le_self_pow (by omega : n.factorization p ≠ 0) p).trans hpv
    have hp2 : p ≠ 2 := by
      intro hp2
      subst p
      exact hodd (Nat.dvd_of_factorization_pos hp0)
    have hp3 : p = 3 := by
      have hpge := hprime.two_le
      have hp4 : p ≠ 4 := by
        intro hp4
        subst p
        norm_num at hprime
      omega
    subst p
    have he : n.factorization 3 ≤ 1 := by
      by_contra he
      have hpow : 3 ^ 2 ≤ 3 ^ n.factorization 3 :=
        Nat.pow_le_pow_right (by decide) (by omega)
      omega
    simpa [(by decide : Nat.Prime 3).factorization_self] using he)
  have hnle : n ≤ 3 := Nat.le_of_dvd (by decide) hd
  omega

/-- Outside the unique odd-part-three frontier, the retained exact formula
already implies the sharp `5/16` head estimate. -/
theorem traceyBinaryFormulaBounds_five_sixteenths_of_oddPart_ne_three
    {s d : ℕ} (hs : 24 ≤ s) (ho3 : ordCompl[2] s ≠ 3)
    (h : TraceyBinaryFormulaBounds s d) :
    16 * d ≤ 5 * s := by
  let a := s.factorization 2
  let o := ordCompl[2] s
  have hs0 : s ≠ 0 := by omega
  have ho0 : o ≠ 0 := (Nat.ordCompl_pos 2 hs0).ne'
  have hodd : ¬2 ∣ o := Nat.not_dvd_ordCompl Nat.prime_two hs0
  by_cases ho1 : o = 1
  · rcases h with hsol | hnsol
    · have hsEq : s = 2 ^ a := by
        have hdecomp := Nat.ordProj_mul_ordCompl_eq_self s 2
        simpa [a, o, ho1] using hdecomp.symm
      have ha5 : 5 ≤ a := by
        by_contra ha
        have hale : a ≤ 4 := by omega
        interval_cases a <;> norm_num [hsEq] at hs
      have hK : traceyBinaryK s = a := by
        rw [hsEq, traceyBinaryK_two_pow]
      have hd : d ≤ a.choose (a / 2) := by
        have hmain := hsol.2
        rw [hK, hsEq] at hmain
        exact Nat.le_of_mul_le_mul_left hmain (pow_pos (by decide) a)
      calc
        16 * d ≤ 16 * a.choose (a / 2) := Nat.mul_le_mul_left 16 hd
        _ ≤ 5 * 2 ^ a := binary_middle_le_five_sixteenths a ha5
        _ = 5 * s := by rw [hsEq]
    · exact (hnsol.1 ho1).elim
  · have hlpp : 5 ≤ largestPrimePower o :=
      largestPrimePower_odd_ge_five o ho0 hodd ho1 (by simpa [o] using ho3)
    have hfive := traceyBinaryFormulaBounds_five_le (by simpa [o] using hlpp) h
    omega

variable {G X A : Type} [Group G] [Finite G] [Finite X] [MulAction G X]
    [FaithfulSMul G X] [MulAction.IsPretransitive G X]
    [AddCommGroup A] [Module (ZMod 2) A] [FiniteDimensional (ZMod 2) A]

/-- The exact formula plus its sole minimally-transitive exceptional input
prove the sharp fixed-space budget for every actual permutation section. -/
theorem binary_permutationSection_invariants_five_sixteenths
    (hTracey : TraceyBinaryFormulaInput)
    (hExceptional : TraceyBinaryExceptionalThreeInput)
    (sigma : Representation (ZMod 2) G A)
    (M : Subrepresentation
      (permutationFunctionRepresentation (ZMod 2) G X))
    (q : M.toRepresentation.IntertwiningMap sigma)
    (hq : Function.Surjective q)
    (hs : 24 ≤ Nat.card X) :
    16 * Module.finrank (ZMod 2) sigma.invariants ≤ 5 * Nat.card X := by
  obtain ⟨P, hdim⟩ :=
    exists_permutationSubrepresentation_head_ge_section_invariants
      sigma M q hq
  by_cases ho3 : ordCompl[2] (Nat.card X) = 3
  · exact (Nat.mul_le_mul_left 16 hdim).trans
      (hExceptional G X P hs ho3)
  · have hformula := hTracey G X P
    have hhead :=
      traceyBinaryFormulaBounds_five_sixteenths_of_oddPart_ne_three
        hs ho3 hformula
    exact (Nat.mul_le_mul_left 16 hdim).trans hhead

end SymmetricSubgroupAsymptotics

end
