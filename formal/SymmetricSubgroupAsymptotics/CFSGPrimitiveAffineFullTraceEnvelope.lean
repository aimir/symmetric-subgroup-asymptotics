import SymmetricSubgroupAsymptotics.PrimitiveAffineNonsolubleFibreEnvelope

/-! A complete actual affine trace envelope with the Schur-one bottom row.
It applies to every primitive affine complement, including soluble and
commutative ones. The price is one prime-log slope, not the translation
dimension. This replaces unnecessary small-order structural inputs when
the literal complement trace already fits the physical window. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics
namespace PrimitiveAffineProfile
variable {L Ω : Type} [Group L] [Finite L] [MulAction L Ω] [Finite Ω]
  [Nontrivial Ω] [FaithfulSMul L Ω]
  (P : PrimitiveAffineProfile L Ω)

def bottomFullSlope : ℝ := Real.logb 2 P.p / P.p

omit [Finite L] [Finite Ω] [Nontrivial Ω] [FaithfulSMul L Ω] in
theorem bottomFullSlope_nonneg : 0 ≤ P.bottomFullSlope := by
  exact div_nonneg
    (Real.logb_nonneg (by norm_num) (by exact_mod_cast P.p_prime.one_le))
    (by positivity)

omit [Finite L] [Finite Ω] [Nontrivial Ω] [FaithfulSMul L Ω] in
theorem bottomFullSlope_le_fixedTargetGamma :
    P.bottomFullSlope ≤ fixedTargetCompositionGamma :=
  prime_log_slope_le_fixedTargetGamma P.p P.p_prime

omit [Finite L] [Finite Ω] [Nontrivial Ω] [FaithfulSMul L Ω] in
theorem bottomFull_rpow_eq_two_rpow (b : ℕ) :
    (P.p : ℝ) ^ ((b : ℝ) / P.p) =
      (2 : ℝ) ^ (P.bottomFullSlope * b) := by
  have hp0 : (0 : ℝ) < P.p := by exact_mod_cast P.p_prime.pos
  calc
    (P.p : ℝ) ^ ((b : ℝ) / P.p) =
        ((2 : ℝ) ^ Real.logb 2 P.p) ^ ((b : ℝ) / P.p) := by
      rw [Real.rpow_logb (by norm_num) (by norm_num) hp0]
    _ = (2 : ℝ) ^ (Real.logb 2 P.p * ((b : ℝ) / P.p)) := by
      rw [← Real.rpow_mul (by norm_num)]
    _ = (2 : ℝ) ^ (P.bottomFullSlope * b) := by
      congr 1
      unfold bottomFullSlope
      ring

/-- Every original normal quotient is included; the same target trace and
original faithful source are retained throughout. -/
theorem completeQuotientWeight_le_fullTraceEnvelope
    (hprimitive : MulAction.IsPreprimitive L Ω)
    (x : Ω) (C : P.ElementaryChart hprimitive)
    (T : FixedTargetCompositionTrace (P.complement x))
    (b : ℕ) (J : Subgroup (Equiv.Perm (Fin b))) :
    completeQuotientWeight (R := L) J ≤
      (Nat.card {N : Subgroup L // N.Normal} : ℝ) *
        (T.envelope.constant * (1 + (b : ℝ)) ^ T.envelope.polynomialDegree) *
        ((Nat.card C.V : ℝ) *
            Nat.card (groupCohomology.H1
              (P.complementRepresentation hprimitive C x)) + 1) *
        (2 : ℝ) ^
          ((fixedTargetCompositionGamma * T.envelope.abelianLength +
              P.bottomFullSlope) * b) := by
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
  let F : ℝ := (P.p : ℝ) ^ ((b : ℝ) / P.p)
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
          P.bottom_epimorphism_card_le_schur_one hprimitive C x J
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
                P.bottomFullSlope) * b) := by
      rw [show F = (2 : ℝ) ^ (P.bottomFullSlope * b) by
        simpa [F] using P.bottomFull_rpow_eq_two_rpow b]
      have hEF : E * (2 : ℝ) ^ (P.bottomFullSlope * b) =
          (2 : ℝ) ^
            ((fixedTargetCompositionGamma * T.envelope.abelianLength +
                P.bottomFullSlope) * b) := by
        dsimp [E]
        rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
        congr 1
        ring
      calc
        (Nat.card {N : Subgroup L // N.Normal} : ℝ) *
              (A * E * (K + 1) *
                (2 : ℝ) ^ (P.bottomFullSlope * b)) =
            (Nat.card {N : Subgroup L // N.Normal} : ℝ) * A *
              (K + 1) * (E * (2 : ℝ) ^ (P.bottomFullSlope * b)) := by ring
        _ = _ := by rw [hEF]
    _ = (Nat.card {N : Subgroup L // N.Normal} : ℝ) *
          (T.envelope.constant * (1 + (b : ℝ)) ^ T.envelope.polynomialDegree) *
          ((Nat.card C.V : ℝ) *
              Nat.card (groupCohomology.H1
                (P.complementRepresentation hprimitive C x)) + 1) *
          (2 : ℝ) ^
            ((fixedTargetCompositionGamma * T.envelope.abelianLength +
                P.bottomFullSlope) * b) := by
      rfl

end PrimitiveAffineProfile
end SymmetricSubgroupAsymptotics

end
