import SymmetricSubgroupAsymptotics.TraceyBinaryOrbitInput
import SymmetricSubgroupAsymptotics.TraceyTernaryEnvelope
import SymmetricSubgroupAsymptotics.BinaryCentralCutNumerics
import SymmetricSubgroupAsymptotics.PermutationBinaryLargeSection
import Mathlib.RepresentationTheory.Invariants

/-!
# The retained binary Tracey formula

This is the precise part of Tracey's induced-module theorem used by the
coupled Schur argument.  In the soluble-transitive alternative it retains
both entries of `E_sol`: the binary part and the central-binomial width.  In
the other alternative it retains the largest-prime-power entry of `E`.

The published theorem is a visible input rather than an axiom.  Everything
after that input in this file is proved: passage from an original permutation
submodule to the fixed space of an arbitrary quotient section, the uniform
`11/32` consequence, and the sharper `1/5` consequence when the odd part has
largest prime-power divisor at least five.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
attribute [local instance] Fintype.ofFinite

namespace SymmetricSubgroupAsymptotics

/-- Tracey's integer `K(s)=sum_{p^a || s} a(p-1)`. -/
def traceyBinaryK (s : ℕ) : ℕ :=
  s.factorization.sum fun p a => a * (p - 1)

/-- The two exact formula alternatives needed here.  The left alternative is
`E_sol`; the right alternative is the largest-prime-power entry of `E`.
The assertion that the right alternative has nontrivial odd part records the
elementary fact that a transitive action of prime-power degree has a soluble
transitive Sylow subgroup. -/
def TraceyBinaryFormulaBounds (s d : ℕ) : Prop :=
  (d ≤ ordProj[2] s ∧
      2 ^ traceyBinaryK s * d ≤
        s * (traceyBinaryK s).choose (traceyBinaryK s / 2)) ∨
  (ordCompl[2] s ≠ 1 ∧
      largestPrimePower (ordCompl[2] s) * d ≤ s)

/-- Visible literature interface: Tracey, Definition 1.5 and Theorem 1.6,
specialized to the binary permutation module. -/
def TraceyBinaryFormulaInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G]
    (X : Type) [Finite X] [MulAction G X] [MulAction.IsPretransitive G X]
    (M : Subrepresentation
      (permutationFunctionRepresentation (ZMod 2) G X)),
    TraceyBinaryFormulaBounds (Nat.card X)
      (Module.finrank (ZMod 2) (M.toRepresentation.IntertwiningMap
        (Representation.trivial (ZMod 2) G (ZMod 2))))

theorem traceyBinaryFormulaBounds_mono {s d e : ℕ}
    (h : TraceyBinaryFormulaBounds s d) (he : e ≤ d) :
    TraceyBinaryFormulaBounds s e := by
  rcases h with h | h
  · left
    exact ⟨he.trans h.1,
      (Nat.mul_le_mul_left (2 ^ traceyBinaryK s) he).trans h.2⟩
  · right
    exact ⟨h.1,
      (Nat.mul_le_mul_left (largestPrimePower (ordCompl[2] s)) he).trans h.2⟩

variable {G X A : Type} [Group G] [Finite G] [Finite X] [MulAction G X]
    [MulAction.IsPretransitive G X]
    [AddCommGroup A] [Module (ZMod 2) A] [FiniteDimensional (ZMod 2) A]

/-- The fixed space of an arbitrary quotient section is dominated by the
head of one literal subrepresentation of the original permutation module.
This is the reusable pullback step behind every formula-level fixed-space
estimate. -/
theorem exists_permutationSubrepresentation_head_ge_section_invariants
    (sigma : Representation (ZMod 2) G A)
    (M : Subrepresentation
      (permutationFunctionRepresentation (ZMod 2) G X))
    (q : M.toRepresentation.IntertwiningMap sigma)
    (hq : Function.Surjective q) :
    ∃ P : Subrepresentation
        (permutationFunctionRepresentation (ZMod 2) G X),
      Module.finrank (ZMod 2) sigma.invariants ≤
        Module.finrank (ZMod 2) (P.toRepresentation.IntertwiningMap
          (Representation.trivial (ZMod 2) G (ZMod 2))) := by
  let P0 : Submodule (ZMod 2) M.toSubmodule :=
    sigma.invariants.comap q.toLinearMap
  let P : Subrepresentation
      (permutationFunctionRepresentation (ZMod 2) G X) := {
    toSubmodule := P0.map M.toSubmodule.subtype
    apply_mem_toSubmodule := by
      intro g v hv
      obtain ⟨v, hv, rfl⟩ := hv
      refine ⟨M.toRepresentation g v, ?_, rfl⟩
      change q (M.toRepresentation g v) ∈ sigma.invariants
      rw [Representation.IntertwiningMap.isIntertwining]
      have hv' : q v ∈ sigma.invariants := hv
      rw [hv' g]
      exact hv' }
  let e : P0 ≃ₗ[ZMod 2] P.toSubmodule :=
    M.toSubmodule.equivSubtypeMap P0
  let q0 : P0 →ₗ[ZMod 2] sigma.invariants :=
    (q.toLinearMap.comp P0.subtype).codRestrict sigma.invariants
      (fun v => v.property)
  let qP : P.toSubmodule →ₗ[ZMod 2] sigma.invariants :=
    q0.comp e.symm.toLinearMap
  have hqP : Function.Surjective qP := by
    intro w
    obtain ⟨v, hv⟩ := hq (w : A)
    have hvP : v ∈ P0 := by
      change q v ∈ sigma.invariants
      rw [hv]
      exact w.property
    refine ⟨e ⟨v, hvP⟩, Subtype.ext ?_⟩
    exact hv
  have htrivial : ∀ (g : G) (v : P.toSubmodule),
      qP (P.toRepresentation g v) = qP v := by
    intro g v
    apply Subtype.ext
    have he : (e.symm (P.toRepresentation g v) : M.toSubmodule) =
        M.toRepresentation g (e.symm v : M.toSubmodule) := by
      apply Subtype.ext
      rfl
    change q (e.symm (P.toRepresentation g v) : M.toSubmodule) =
      q (e.symm v : M.toSubmodule)
    rw [he]
    rw [Representation.IntertwiningMap.isIntertwining]
    exact (e.symm v).property g
  let qcoin : P.toRepresentation.Coinvariants →ₗ[ZMod 2] sigma.invariants :=
    Representation.Coinvariants.lift P.toRepresentation qP (by
      intro g
      apply LinearMap.ext
      exact htrivial g)
  have hqcoin : Function.Surjective qcoin := by
    intro w
    obtain ⟨v, hv⟩ := hqP w
    exact ⟨Representation.Coinvariants.mk P.toRepresentation v, hv⟩
  refine ⟨P, ?_⟩
  have hdim := LinearMap.finrank_le_finrank_of_surjective hqcoin
  rw [← representationHead_finrank_eq_coinvariants] at hdim
  exact hdim

/-- Pull the fixed space of an arbitrary quotient section back to its actual
preimage in the original permutation submodule.  Its trivial quotient factors
through the intrinsic coinvariants of that preimage, so the published head
bound applies without embedding the section into the permutation module. -/
theorem traceyBinaryFormulaBounds_section_invariants
    (hTracey : TraceyBinaryFormulaInput)
    (sigma : Representation (ZMod 2) G A)
    (M : Subrepresentation
      (permutationFunctionRepresentation (ZMod 2) G X))
    (q : M.toRepresentation.IntertwiningMap sigma)
    (hq : Function.Surjective q) :
    TraceyBinaryFormulaBounds (Nat.card X)
      (Module.finrank (ZMod 2) sigma.invariants) := by
  obtain ⟨P, hdim⟩ :=
    exists_permutationSubrepresentation_head_ge_section_invariants
      sigma M q hq
  exact traceyBinaryFormulaBounds_mono (hTracey G X P) hdim

theorem traceyBinaryK_two_pow (a : ℕ) :
    traceyBinaryK (2 ^ a) = a := by
  simp [traceyBinaryK, Nat.prime_two.factorization_pow]

/-- The middle binomial density is at most `11/32` from exponent five
onward.  Pascal's doubling inequality propagates the exact endpoint. -/
theorem binary_middle_le_eleven_thirtySecond (a : ℕ) (ha : 5 ≤ a) :
    32 * a.choose (a / 2) ≤ 11 * 2 ^ a := by
  induction a, ha using Nat.le_induction with
  | base => decide
  | succ a ha ih =>
      calc
        32 * (a + 1).choose ((a + 1) / 2) ≤
            32 * (2 * a.choose (a / 2)) :=
          Nat.mul_le_mul_left 32 (binary_middle_succ_le_twice a)
        _ = 2 * (32 * a.choose (a / 2)) := by ring
        _ ≤ 2 * (11 * 2 ^ a) := Nat.mul_le_mul_left 2 ih
        _ = 11 * 2 ^ (a + 1) := by rw [pow_succ]; ring

theorem largestPrimePower_odd_ge_three (n : ℕ) (hn : n ≠ 0)
    (hodd : ¬2 ∣ n) (h1 : n ≠ 1) :
    3 ≤ largestPrimePower n := by
  by_cases h3 : 3 ∣ n
  · have hf : n.factorization 3 ≠ 0 := by
      exact (Nat.prime_three.factorization_pos_of_dvd hn h3).ne'
    have hp : 3 ≤ 3 ^ n.factorization 3 :=
      Nat.le_self_pow (by omega) 3
    exact hp.trans (primePower_le_largestPrimePower n 3)
  · exact (largestPrimePower_ge_four n hn h3 h1 (by
      intro h2
      subst n
      exact hodd (by decide))).trans' (by decide)

theorem largestPrimePower_le_self (n : ℕ) (hn : n ≠ 0) :
    largestPrimePower n ≤ n := by
  rw [largestPrimePower]
  apply max_le (by omega)
  apply Finset.sup_le
  intro p hp
  have hprime : p.Prime := Nat.prime_of_mem_primeFactors
    (show p ∈ n.primeFactors from hp)
  exact Nat.le_of_dvd (Nat.pos_of_ne_zero hn)
    ((hprime.pow_dvd_iff_le_factorization hn).mpr le_rfl)

theorem primePower_le_largestPrimePower_of_dvd
    {n p e : ℕ} (hp : p.Prime) (hn : n ≠ 0) (hdiv : p ^ e ∣ n) :
    p ^ e ≤ largestPrimePower n := by
  have he : e ≤ n.factorization p :=
    (hp.pow_dvd_iff_le_factorization hn).mp hdiv
  exact (Nat.pow_le_pow_right hp.pos he).trans
    (primePower_le_largestPrimePower n p)

/-- Every retained formula branch gives the uniform fixed-space estimate
used by the coupled Schur calculation. -/
theorem traceyBinaryFormulaBounds_eleven_thirtySecond
    {s d : ℕ} (hs : 24 ≤ s)
    (h : TraceyBinaryFormulaBounds s d) :
    32 * d ≤ 11 * s := by
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
        32 * d ≤ 32 * a.choose (a / 2) := Nat.mul_le_mul_left 32 hd
        _ ≤ 11 * 2 ^ a := binary_middle_le_eleven_thirtySecond a ha5
        _ = 11 * s := by rw [hsEq]
    · exact (hnsol.1 ho1).elim
  · have ho2 : o ≠ 2 := by
      intro h2
      exact hodd (h2.symm ▸ dvd_refl 2)
    have ho3 : 3 ≤ o := by
      have hoOne : 1 ≤ o := Nat.one_le_iff_ne_zero.mpr ho0
      have hoTwo : 2 ≤ o := lt_of_le_of_ne hoOne (Ne.symm ho1)
      exact Nat.succ_le_iff.mpr (lt_of_le_of_ne hoTwo (Ne.symm ho2))
    rcases h with hsol | hnsol
    · have hd := Nat.mul_le_mul_left 3 hsol.1
      have hpart : 3 * ordProj[2] s ≤ ordProj[2] s * o := by
        simpa [Nat.mul_comm] using Nat.mul_le_mul_right (ordProj[2] s) ho3
      have hdecomp := Nat.ordProj_mul_ordCompl_eq_self s 2
      have hthree : 3 * d ≤ s := hd.trans (by simpa [o] using hpart.trans_eq hdecomp)
      omega
    · have hlpp : 3 ≤ largestPrimePower o :=
        largestPrimePower_odd_ge_three o ho0 hodd ho1
      have hthree : 3 * d ≤ s :=
        (Nat.mul_le_mul_right d hlpp).trans (by simpa [o] using hnsol.2)
      omega

/-- If the odd part has a prime-power divisor of size at least five, both
formula alternatives give the sharper one-fifth estimate. -/
theorem traceyBinaryFormulaBounds_five_le
    {s d : ℕ} (hfive : 5 ≤ largestPrimePower (ordCompl[2] s))
    (h : TraceyBinaryFormulaBounds s d) :
    5 * d ≤ s := by
  rcases h with hsol | hnsol
  · have hs0 : s ≠ 0 := by
      intro hs
      subst s
      norm_num [largestPrimePower] at hfive
    let o := ordCompl[2] s
    have ho5 : 5 ≤ o := hfive.trans
      (largestPrimePower_le_self o (Nat.ordCompl_pos 2 hs0).ne')
    calc
      5 * d ≤ 5 * ordProj[2] s := Nat.mul_le_mul_left 5 hsol.1
      _ ≤ ordProj[2] s * ordCompl[2] s := by
        simpa [Nat.mul_comm] using
          Nat.mul_le_mul_right (ordProj[2] s) ho5
      _ = s := Nat.ordProj_mul_ordCompl_eq_self s 2
  · exact (Nat.mul_le_mul_right d hfive).trans hnsol.2

/-- The only even divisors of `180` at least `24` have odd part with a
prime-power divisor of size at least five.  This is the finite arithmetic
left after the faithful row embeds in `GL₂(4)`. -/
theorem largestPrimePower_ordCompl_two_ge_five_of_dvd_180
    {s : ℕ} (hdiv : s ∣ 180) (hs : 24 ≤ s) (heven : Even s) :
    5 ≤ largestPrimePower (ordCompl[2] s) := by
  have hle : s ≤ 180 := Nat.le_of_dvd (by decide) hdiv
  have hcases : s = 30 ∨ s = 36 ∨ s = 60 ∨ s = 90 ∨ s = 180 := by
    interval_cases s <;> norm_num at hdiv <;> norm_num at heven <;> norm_num
  rcases hcases with rfl | rfl | rfl | rfl | rfl
  · have h := primePower_le_largestPrimePower_of_dvd (e := 1) Nat.prime_five
      (Nat.ordCompl_pos 2 (by decide : (30 : ℕ) ≠ 0)).ne'
      (Nat.dvd_ordCompl_of_dvd_not_dvd (by decide : 5 ∣ 30) (by decide : ¬2 ∣ 5))
    simpa using h
  · have h := primePower_le_largestPrimePower_of_dvd (e := 2) Nat.prime_three
      (Nat.ordCompl_pos 2 (by decide : (36 : ℕ) ≠ 0)).ne'
      (Nat.dvd_ordCompl_of_dvd_not_dvd (by decide : 3 ^ 2 ∣ 36)
        (by decide : ¬2 ∣ 3 ^ 2))
    omega
  · have h := primePower_le_largestPrimePower_of_dvd (e := 1) Nat.prime_five
      (Nat.ordCompl_pos 2 (by decide : (60 : ℕ) ≠ 0)).ne'
      (Nat.dvd_ordCompl_of_dvd_not_dvd (by decide : 5 ∣ 60) (by decide : ¬2 ∣ 5))
    simpa using h
  · have h := primePower_le_largestPrimePower_of_dvd (e := 1) Nat.prime_five
      (Nat.ordCompl_pos 2 (by decide : (90 : ℕ) ≠ 0)).ne'
      (Nat.dvd_ordCompl_of_dvd_not_dvd (by decide : 5 ∣ 90) (by decide : ¬2 ∣ 5))
    simpa using h
  · have h := primePower_le_largestPrimePower_of_dvd (e := 1) Nat.prime_five
      (Nat.ordCompl_pos 2 (by decide : (180 : ℕ) ≠ 0)).ne'
      (Nat.dvd_ordCompl_of_dvd_not_dvd (by decide : 5 ∣ 180) (by decide : ¬2 ∣ 5))
    simpa using h

private theorem traceyBinaryFormulaBounds_three_le_of_oddPart_ne_one
    {s d : ℕ} (hs0 : s ≠ 0) (ho1 : ordCompl[2] s ≠ 1)
    (h : TraceyBinaryFormulaBounds s d) :
    3 * d ≤ s := by
  let o := ordCompl[2] s
  have ho0 : o ≠ 0 := (Nat.ordCompl_pos 2 hs0).ne'
  have hodd : ¬2 ∣ o := Nat.not_dvd_ordCompl Nat.prime_two hs0
  have ho2 : o ≠ 2 := by
    intro h2
    exact hodd (h2.symm ▸ dvd_refl 2)
  have ho3 : 3 ≤ o := by
    have hoOne : 1 ≤ o := Nat.one_le_iff_ne_zero.mpr ho0
    have hoTwo : 2 ≤ o := lt_of_le_of_ne hoOne (Ne.symm ho1)
    exact Nat.succ_le_iff.mpr (lt_of_le_of_ne hoTwo (Ne.symm ho2))
  rcases h with hsol | hnsol
  · calc
      3 * d ≤ 3 * ordProj[2] s := Nat.mul_le_mul_left 3 hsol.1
      _ ≤ ordProj[2] s * ordCompl[2] s := by
        simpa [o, Nat.mul_comm] using
          Nat.mul_le_mul_right (ordProj[2] s) ho3
      _ = s := Nat.ordProj_mul_ordCompl_eq_self s 2
  · have hlpp : 3 ≤ largestPrimePower o :=
      largestPrimePower_odd_ge_three o ho0 hodd ho1
    exact (Nat.mul_le_mul_right d hlpp).trans (by simpa [o] using hnsol.2)

private theorem traceyBinaryFormulaBounds_two_le
    {s d : ℕ} (hs : 2 ≤ s) (h : TraceyBinaryFormulaBounds s d) :
    2 * d ≤ s := by
  by_cases ho1 : ordCompl[2] s = 1
  · rcases h with hsol | hnsol
    · let a := s.factorization 2
      have hsEq : s = 2 ^ a := by
        have hdecomp := Nat.ordProj_mul_ordCompl_eq_self s 2
        simpa [a, ho1] using hdecomp.symm
      have ha1 : 1 ≤ a := by
        by_contra ha
        have ha0 : a = 0 := by omega
        norm_num [hsEq, ha0] at hs
      have hK : traceyBinaryK s = a := by
        rw [hsEq, traceyBinaryK_two_pow]
      have hd : d ≤ a.choose (a / 2) := by
        have hmain := hsol.2
        rw [hK, hsEq] at hmain
        exact Nat.le_of_mul_le_mul_left hmain (pow_pos (by decide) a)
      exact (Nat.mul_le_mul_left 2 hd).trans (by
        simpa [hsEq] using binary_middle_twice_le_power a ha1)
    · exact (hnsol.1 ho1).elim
  · have hs0 : s ≠ 0 := by omega
    have hthree := traceyBinaryFormulaBounds_three_le_of_oddPart_ne_one
      hs0 ho1 h
    omega

private theorem traceyBinaryFormulaBounds_three_eighths
    {s d : ℕ} (hs : 8 ≤ s) (h : TraceyBinaryFormulaBounds s d) :
    8 * d ≤ 3 * s := by
  by_cases ho1 : ordCompl[2] s = 1
  · rcases h with hsol | hnsol
    · let a := s.factorization 2
      have hsEq : s = 2 ^ a := by
        have hdecomp := Nat.ordProj_mul_ordCompl_eq_self s 2
        simpa [a, ho1] using hdecomp.symm
      have ha3 : 3 ≤ a := by
        by_contra ha
        have hale : a ≤ 2 := by omega
        interval_cases a <;> norm_num [hsEq] at hs
      have hK : traceyBinaryK s = a := by
        rw [hsEq, traceyBinaryK_two_pow]
      have hd : d ≤ a.choose (a / 2) := by
        have hmain := hsol.2
        rw [hK, hsEq] at hmain
        exact Nat.le_of_mul_le_mul_left hmain (pow_pos (by decide) a)
      exact (Nat.mul_le_mul_left 8 hd).trans (by
        simpa [hsEq] using binary_middle_le_three_eighths a ha3)
    · exact (hnsol.1 ho1).elim
  · have hs0 : s ≠ 0 := by omega
    have hthree := traceyBinaryFormulaBounds_three_le_of_oddPart_ne_one
      hs0 ho1 h
    omega

/-- The retained exact formula implies the earlier coarse orbit interface;
consumers therefore need only one literature hypothesis. -/
theorem TraceyBinaryFormulaInput.toOrbitInput
    (hTracey : TraceyBinaryFormulaInput) :
    TraceyBinaryOrbitInput := by
  intro G _ _ X _ _ _ M
  have h := hTracey G X M
  rw [traceyBinaryOrbitCap]
  split_ifs with h1 h8
  · rw [h1] at h
    rcases h with hsol | hnsol
    · simpa using hsol.1
    · norm_num at hnsol
  · apply (Nat.le_div_iff_mul_le (by decide : 0 < 8)).2
    simpa [Nat.mul_comm] using
      traceyBinaryFormulaBounds_three_eighths h8 h
  · by_cases hs0 : Nat.card X = 0
    · rw [hs0] at h ⊢
      rcases h with hsol | hnsol
      · norm_num [traceyBinaryK] at hsol ⊢
        exact hsol.2
      · norm_num [largestPrimePower] at hnsol ⊢
        exact hnsol
    · have hs2 : 2 ≤ Nat.card X := by omega
      apply (Nat.le_div_iff_mul_le (by decide : 0 < 2)).2
      simpa [Nat.mul_comm] using traceyBinaryFormulaBounds_two_le hs2 h

end SymmetricSubgroupAsymptotics

end
