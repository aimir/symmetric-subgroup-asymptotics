import SymmetricSubgroupAsymptotics.PrimitiveAffineComplementComposition

/-!
# Complete nonsoluble primitive-affine fibre envelope

This file combines the literal normal-axis reduction, the strict Schur bound
on the original affine bottom fibre, and the traced fixed-target envelope of
the actual point stabilizer.  No catalogue or asymptotic absorption is used:
the result is a pointwise estimate for every permutation source.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace PrimitiveAffineProfile

variable {L Ω : Type} [Group L] [Finite L] [MulAction L Ω] [Finite Ω]
  [Nontrivial Ω] [FaithfulSMul L Ω]
  (P : PrimitiveAffineProfile L Ω)

/-- The base-two exponent contributed by the strict one-half Schur row of
the translation module. -/
def bottomHalfSlope : ℝ :=
  Real.logb 2 P.p / (2 * P.p)

omit [Finite L] [Finite Ω] [Nontrivial Ω] [FaithfulSMul L Ω] in
theorem bottomHalfSlope_nonneg : 0 ≤ P.bottomHalfSlope := by
  unfold bottomHalfSlope
  exact div_nonneg
    (Real.logb_nonneg (by norm_num) (by exact_mod_cast P.p_prime.one_le))
    (by positivity)

/-- Rewrite the strict affine bottom factor in base two. -/
omit [Finite L] [Finite Ω] [Nontrivial Ω] [FaithfulSMul L Ω] in
theorem bottomHalf_rpow_eq_two_rpow
    (b : ℕ) :
    (P.p : ℝ) ^ (((1 : ℝ) / 2) * ((b : ℝ) / P.p)) =
      (2 : ℝ) ^ (P.bottomHalfSlope * b) := by
  have hp0 : (0 : ℝ) < P.p := by exact_mod_cast P.p_prime.pos
  calc
    (P.p : ℝ) ^ (((1 : ℝ) / 2) * ((b : ℝ) / P.p)) =
        ((2 : ℝ) ^ Real.logb 2 P.p) ^
          (((1 : ℝ) / 2) * ((b : ℝ) / P.p)) := by
      rw [Real.rpow_logb (by norm_num) (by norm_num) hp0]
    _ =
        (2 : ℝ) ^
          (Real.logb 2 P.p * (((1 : ℝ) / 2) * ((b : ℝ) / P.p))) := by
      rw [← Real.rpow_mul (by norm_num)]
    _ = (2 : ℝ) ^ (P.bottomHalfSlope * b) := by
      congr 1
      unfold bottomHalfSlope
      field_simp

/-- The complete pointwise envelope obtained from one traced complement.
The coefficient contains only fixed data from the literal target action. -/
theorem completeQuotientWeight_le_nonsolubleEnvelope
    (hprimitive : MulAction.IsPreprimitive L Ω)
    (x : Ω) (C : P.ElementaryChart hprimitive)
    (T : FixedTargetCompositionTrace (P.complement x))
    (hnonsolvable : ¬ IsSolvable (P.complement x))
    (b : ℕ) (J : Subgroup (Equiv.Perm (Fin b))) :
    completeQuotientWeight (R := L) J ≤
      (Nat.card {N : Subgroup L // N.Normal} : ℝ) *
        (T.envelope.constant * (1 + (b : ℝ)) ^ T.envelope.polynomialDegree) *
        ((Nat.card C.V : ℝ) *
            Nat.card (groupCohomology.H1
              (P.complementRepresentation hprimitive C x)) + 1) *
        (2 : ℝ) ^
          ((fixedTargetCompositionGamma * T.envelope.abelianLength +
              P.bottomHalfSlope) * b) := by
  letI : Fact P.p.Prime := C.primeFact
  letI : Finite C.V := Finite.of_injective
    (fun v : C.V => C.equiv.symm (Multiplicative.ofAdd v))
    C.equiv.symm.injective
  let R := P.complement x
  let A : ℝ := T.envelope.constant *
    (1 + (b : ℝ)) ^ T.envelope.polynomialDegree
  let K : ℝ := (Nat.card C.V : ℝ) *
    Nat.card (groupCohomology.H1
      (P.complementRepresentation hprimitive C x))
  let E : ℝ := (2 : ℝ) ^
    ((fixedTargetCompositionGamma * T.envelope.abelianLength) * b)
  let F : ℝ := (P.p : ℝ) ^ (((1 : ℝ) / 2) * ((b : ℝ) / P.p))
  have hA : 0 ≤ A := mul_nonneg T.envelope.constant_nonneg (by positivity)
  have hK : 0 ≤ K := by positivity
  have hE : 0 ≤ E := Real.rpow_nonneg (by norm_num) _
  have hF : 1 ≤ F := by
    unfold F
    apply Real.one_le_rpow
    · exact_mod_cast P.p_prime.one_lt.le
    · positivity
  have hR : completeQuotientWeight (R := R) J ≤ A * E := by
    simpa [R, A, E] using T.envelope.bound b J
  have hepiR : (Nat.card (GroupEpimorphism J R) : ℝ) ≤
      completeQuotientWeight (R := R) J := by
    exact card_groupEpimorphism_le_completeQuotientWeight J
      (R := R) (Q := R) ⟨⊥, inferInstance⟩
      QuotientGroup.quotientBot.symm
  have hepiL : (Nat.card (GroupEpimorphism J L) : ℝ) ≤
      A * E * K * F := by
    calc
      (Nat.card (GroupEpimorphism J L) : ℝ) ≤
          Nat.card (GroupEpimorphism J R) * K * F := by
        simpa [R, K, F, mul_assoc] using
          P.bottom_epimorphism_card_le_schur_half hprimitive C x
            (noncommutative_of_not_isSolvable hnonsolvable) J
      _ ≤ completeQuotientWeight (R := R) J * K * F :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hepiR hK) (by positivity)
      _ ≤ (A * E) * K * F :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hR hK) (by positivity)
  have hsum : (Nat.card (GroupEpimorphism J L) : ℝ) +
      completeQuotientWeight (R := R) J ≤ A * E * (K + 1) * F := by
    have hAEF : A * E ≤ A * E * F := by
      calc
        A * E = A * E * 1 := by ring
        _ ≤ A * E * F :=
          mul_le_mul_of_nonneg_left hF (mul_nonneg hA hE)
    calc
      (Nat.card (GroupEpimorphism J L) : ℝ) +
          completeQuotientWeight (R := R) J ≤
          A * E * K * F + A * E := add_le_add hepiL hR
      _ ≤ A * E * K * F + A * E * F := by
        exact add_le_add_right hAEF _
      _ = A * E * (K + 1) * F := by ring
  have hnormal := P.completeQuotientWeight_le_normalAxis_mul
    hprimitive x J
  calc
    completeQuotientWeight (R := L) J ≤
        (Nat.card {N : Subgroup L // N.Normal} : ℝ) *
          ((Nat.card (GroupEpimorphism J L) : ℝ) +
            completeQuotientWeight (R := R) J) := by
      simpa [R] using hnormal
    _ ≤ (Nat.card {N : Subgroup L // N.Normal} : ℝ) *
          (A * E * (K + 1) * F) :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = (Nat.card {N : Subgroup L // N.Normal} : ℝ) * A * (K + 1) *
          (2 : ℝ) ^
            ((fixedTargetCompositionGamma * T.envelope.abelianLength +
                P.bottomHalfSlope) * b) := by
      rw [show F = (2 : ℝ) ^ (P.bottomHalfSlope * b) by
        simpa [F] using P.bottomHalf_rpow_eq_two_rpow b]
      have hEF : E * (2 : ℝ) ^ (P.bottomHalfSlope * b) =
          (2 : ℝ) ^
            ((fixedTargetCompositionGamma * T.envelope.abelianLength +
                P.bottomHalfSlope) * b) := by
        dsimp [E]
        rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
        congr 1
        ring
      calc
        (Nat.card {N : Subgroup L // N.Normal} : ℝ) *
              (A * E * (K + 1) *
                (2 : ℝ) ^ (P.bottomHalfSlope * b)) =
            (Nat.card {N : Subgroup L // N.Normal} : ℝ) * A *
              (K + 1) * (E * (2 : ℝ) ^ (P.bottomHalfSlope * b)) := by ring
        _ = _ := by rw [hEF]
    _ = (Nat.card {N : Subgroup L // N.Normal} : ℝ) *
          (T.envelope.constant * (1 + (b : ℝ)) ^ T.envelope.polynomialDegree) *
          ((Nat.card C.V : ℝ) *
              Nat.card (groupCohomology.H1
                (P.complementRepresentation hprimitive C x)) + 1) *
          (2 : ℝ) ^
            ((fixedTargetCompositionGamma * T.envelope.abelianLength +
                P.bottomHalfSlope) * b) := by
      rfl

end PrimitiveAffineProfile
end SymmetricSubgroupAsymptotics

end
