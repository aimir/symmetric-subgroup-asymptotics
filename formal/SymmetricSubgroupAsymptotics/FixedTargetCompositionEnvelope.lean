import SymmetricSubgroupAsymptotics.MinimalNormalCompositionCharts
import SymmetricSubgroupAsymptotics.TrivialQuotientComparator
import SymmetricSubgroupAsymptotics.Non2PreE7SmallAdditiveInstances
import SymmetricSubgroupAsymptotics.Non2PreE7SaprimOddCyclicAffine

/-!
# The fixed-target composition envelope

This file inducts over actual minimal normal subgroups.  Elementary layers
use the retained-axis Schur theorem; nonabelian layers use the literal
semisimple outer-fibre theorem.  The result is a polynomial times a linear
exponent, with one `log₂(3)/3` charge per abelian composition edge.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics

/-- The worst prime-field logarithmic slope. -/
def fixedTargetCompositionGamma : ℝ := Real.logb 2 3 / 3

theorem prime_log_slope_le_fixedTargetGamma
    (p : ℕ) (hp : p.Prime) :
    Real.logb 2 p / p ≤ fixedTargetCompositionGamma := by
  by_cases hp2 : p = 2
  · subst p
    simpa [fixedTargetCompositionGamma,
      Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2)] using
      half_le_logThreeThird
  · have hpge2 : 2 ≤ p := hp.two_le
    have hp3 : 3 ≤ p := by omega
    exact primeLogSlope_le_three hp3

/-- A complete fixed-target bound with explicit polynomial and abelian
composition-edge parameters. -/
structure FixedTargetCompositionEnvelope
    (G : Type) [Group G] [Finite G] where
  constant : ℝ
  polynomialDegree : ℕ
  abelianLength : ℕ
  constant_nonneg : 0 ≤ constant
  bound : ∀ b (J : Subgroup (Equiv.Perm (Fin b))),
    completeQuotientWeight (R := G) J ≤
      constant * (1 + (b : ℝ)) ^ polynomialDegree *
        (2 : ℝ) ^
          ((fixedTargetCompositionGamma * abelianLength) * (b : ℝ))

namespace FixedTargetCompositionEnvelope

private theorem rpow_eq_two_rpow_logb
    {B : ℝ} (hB : 0 < B) (x : ℝ) :
    B ^ x = (2 : ℝ) ^ (Real.logb 2 B * x) := by
  rw [Real.rpow_mul (by norm_num),
    Real.rpow_logb (by norm_num) (by norm_num) hB]

/-- The trivial target starts the induction. -/
def ofSubsingleton
    (G : Type) [Group G] [Finite G] [Subsingleton G] :
    FixedTargetCompositionEnvelope G where
  constant := 1
  polynomialDegree := 0
  abelianLength := 0
  constant_nonneg := by norm_num
  bound := by
    intro b J
    rw [completeQuotientWeight_eq_one_of_subsingleton (R := G) J]
    norm_num

/-- Rewrite a prime-field elementary exponent in base two. -/
theorem prime_rpow_le_gamma
    (p d b : ℕ) (hp : p.Prime) :
    (p : ℝ) ^ ((d : ℝ) * ((b : ℝ) / p)) ≤
      (2 : ℝ) ^
        ((fixedTargetCompositionGamma * d) * (b : ℝ)) := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have heq :
      (p : ℝ) ^ ((d : ℝ) * ((b : ℝ) / p)) =
        (2 : ℝ) ^
          (((Real.logb 2 p / p) * d) * (b : ℝ)) := by
    calc
      (p : ℝ) ^ ((d : ℝ) * ((b : ℝ) / p)) =
          (2 : ℝ) ^
            (Real.logb 2 p * ((d : ℝ) * ((b : ℝ) / p))) := by
        exact rpow_eq_two_rpow_logb hp0 _
      _ = (2 : ℝ) ^ (((Real.logb 2 p / p) * d) * (b : ℝ)) := by
        congr 1
        field_simp
  rw [heq]
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
  have hs := prime_log_slope_le_fixedTargetGamma p hp
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hs (Nat.cast_nonneg d))
    (Nat.cast_nonneg b)

/-- Add one elementary minimal normal layer. -/
noncomputable def elementaryStep
    {G : Type} [Group G] [Finite G]
    (E : Subgroup G) [E.Normal]
    (C : ElementaryMinimalNormalChart E) [Finite C.quotientRepresentation]
    (Q : FixedTargetCompositionEnvelope (G ⧸ E)) :
    FixedTargetCompositionEnvelope G where
  constant := elementaryLayerEnvelopeConstant C.p
      (QuotientGroup.mk' E) C.quotientRepresentation C.originalKernelChart *
    Q.constant
  polynomialDegree := Q.polynomialDegree
  abelianLength := Module.finrank (ZMod C.p) C.V + Q.abelianLength
  constant_nonneg := mul_nonneg
    (elementaryLayerEnvelopeConstant_nonneg C.p
      (QuotientGroup.mk' E) C.quotientRepresentation C.originalKernelChart)
    Q.constant_nonneg
  bound := by
    intro b J
    let L := elementaryLayerEnvelopeConstant C.p
      (QuotientGroup.mk' E) C.quotientRepresentation C.originalKernelChart
    let d := Module.finrank (ZMod C.p) C.V
    have hlayer := completeQuotientWeight_le_elementaryLayer C.p
      (QuotientGroup.mk' E) (QuotientGroup.mk'_surjective E)
      C.quotientRepresentation C.originalKernelChart J
    have hq := Q.bound b J
    have hp := prime_rpow_le_gamma C.p d b C.p_prime
    calc
      completeQuotientWeight (R := G) J ≤
          L * (C.p : ℝ) ^ ((d : ℝ) * ((b : ℝ) / C.p)) *
            completeQuotientWeight (R := G ⧸ E) J := by
              simpa [L, d] using hlayer
      _ ≤ L * (C.p : ℝ) ^ ((d : ℝ) * ((b : ℝ) / C.p)) *
          (Q.constant * (1 + (b : ℝ)) ^ Q.polynomialDegree *
            (2 : ℝ) ^
              ((fixedTargetCompositionGamma * Q.abelianLength) * (b : ℝ))) :=
        mul_le_mul_of_nonneg_left hq
          (mul_nonneg (elementaryLayerEnvelopeConstant_nonneg C.p
            (QuotientGroup.mk' E) C.quotientRepresentation C.originalKernelChart)
            (Real.rpow_nonneg (by positivity) _))
      _ ≤ L *
          (2 : ℝ) ^ ((fixedTargetCompositionGamma * d) * (b : ℝ)) *
          (Q.constant * (1 + (b : ℝ)) ^ Q.polynomialDegree *
            (2 : ℝ) ^
              ((fixedTargetCompositionGamma * Q.abelianLength) * (b : ℝ))) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hp
            (elementaryLayerEnvelopeConstant_nonneg C.p
              (QuotientGroup.mk' E) C.quotientRepresentation C.originalKernelChart))
          (mul_nonneg
            (mul_nonneg Q.constant_nonneg (by positivity))
            (Real.rpow_nonneg (by norm_num) _))
      _ = (L * Q.constant) * (1 + (b : ℝ)) ^ Q.polynomialDegree *
          (2 : ℝ) ^
            ((fixedTargetCompositionGamma *
              ((d + Q.abelianLength : ℕ) : ℝ)) * (b : ℝ)) := by
        rw [show
          (fixedTargetCompositionGamma *
              ((d + Q.abelianLength : ℕ) : ℝ)) * (b : ℝ) =
            (fixedTargetCompositionGamma * d) * (b : ℝ) +
              (fixedTargetCompositionGamma * Q.abelianLength) * (b : ℝ) by
          push_cast
          ring,
          Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
        ring

/-! ## Polynomial payment for a fixed semisimple layer -/

private theorem factorial_le_two_pow_sq (b : ℕ) :
    b.factorial ≤ 2 ^ (b * b) := by
  calc
    b.factorial ≤ b ^ b := b.factorial_le_pow
    _ ≤ (2 ^ b) ^ b := Nat.pow_le_pow_left (Nat.le_of_lt b.lt_two_pow_self) b
    _ = 2 ^ (b * b) := by rw [pow_mul]

theorem source_logb_card_le_sq
    {b : ℕ} (J : Subgroup (Equiv.Perm (Fin b))) :
    Real.logb 2 (Nat.card J) ≤ (b : ℝ) ^ 2 := by
  have hcard : Nat.card J ≤ b.factorial := by
    calc
      Nat.card J ≤ Nat.card (Equiv.Perm (Fin b)) :=
        Subgroup.card_le_card_group J
      _ = b.factorial := by rw [Nat.card_perm, Nat.card_fin]
  have hpow : Nat.card J ≤ 2 ^ (b * b) :=
    hcard.trans (factorial_le_two_pow_sq b)
  have hlog := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
    (by exact_mod_cast (Nat.card_pos (α := J)))
    (by exact_mod_cast hpow : (Nat.card J : ℝ) ≤ (2 ^ (b * b) : ℕ))
  calc
    Real.logb 2 (Nat.card J) ≤
        Real.logb 2 ((2 ^ (b * b) : ℕ) : ℝ) := hlog
    _ = (b : ℝ) ^ 2 := by
      rw [Nat.cast_pow, Nat.cast_ofNat, Real.logb_pow,
        Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2), mul_one,
        Nat.cast_mul]
      ring

/-- The fixed coefficient which pays the automorphism and denominator of
each displayed simple factor. -/
def semisimplePolynomialConstant
    {G : Type} [Group G] {E : Subgroup G}
    (C : SemisimpleNormalChart E) : ℝ :=
  ∏ i, (1 +
    (Nat.card (C.factor i ≃* C.factor i) : ℝ) /
      Real.logb 2 (Nat.card (C.factor i)))

theorem semisimplePolynomialConstant_nonneg
    {G : Type} [Group G] {E : Subgroup G}
    (C : SemisimpleNormalChart E) :
    0 ≤ semisimplePolynomialConstant C := by
  unfold semisimplePolynomialConstant
  apply Finset.prod_nonneg
  intro i _
  exact add_nonneg zero_le_one
    (div_nonneg (Nat.cast_nonneg _) (C.logb_card_pos i).le)

theorem semisimple_outerFactor_le_polynomial
    {G : Type} [Group G] {E : Subgroup G}
    (C : SemisimpleNormalChart E)
    {b : ℕ} (J : Subgroup (Equiv.Perm (Fin b))) :
    C.outerFactor (Real.logb 2 (Nat.card J)) ≤
      semisimplePolynomialConstant C *
        (1 + (b : ℝ)) ^ (2 * Fintype.card C.ι) := by
  let L : ℝ := Real.logb 2 (Nat.card J)
  have hL0 : 0 ≤ L := Real.logb_nonneg (by norm_num)
    (by exact_mod_cast Nat.card_pos (α := J))
  have hL : L ≤ (b : ℝ) ^ 2 := source_logb_card_le_sq J
  have hbase : 1 + L ≤ (1 + (b : ℝ)) ^ 2 := by
    have hb : 0 ≤ (b : ℝ) := by positivity
    nlinarith
  have hfactor : ∀ i : C.ι,
      1 + C.factorWeight L i ≤
        (1 + (Nat.card (C.factor i ≃* C.factor i) : ℝ) /
          Real.logb 2 (Nat.card (C.factor i))) *
            (1 + (b : ℝ)) ^ 2 := by
    intro i
    let c : ℝ := (Nat.card (C.factor i ≃* C.factor i) : ℝ) /
      Real.logb 2 (Nat.card (C.factor i))
    have hc : 0 ≤ c := by
      dsimp [c]
      exact div_nonneg (Nat.cast_nonneg _) (C.logb_card_pos i).le
    have hid : C.factorWeight L i = c * L := by
      unfold SemisimpleNormalChart.factorWeight
      dsimp [c]
      ring
    rw [hid]
    calc
      1 + c * L ≤ (1 + c) * (1 + L) := by nlinarith
      _ ≤ (1 + c) * (1 + (b : ℝ)) ^ 2 :=
        mul_le_mul_of_nonneg_left hbase (by linarith)
  unfold SemisimpleNormalChart.outerFactor semisimplePolynomialConstant
  calc
    (∏ i : C.ι, (1 + C.factorWeight L i)) ≤
        ∏ i : C.ι,
          ((1 + (Nat.card (C.factor i ≃* C.factor i) : ℝ) /
            Real.logb 2 (Nat.card (C.factor i))) *
              (1 + (b : ℝ)) ^ 2) :=
      Finset.prod_le_prod
        (fun i _ => add_nonneg zero_le_one (C.factorWeight_nonneg hL0 i))
        (fun i _ => hfactor i)
    _ = (∏ i : C.ι,
          (1 + (Nat.card (C.factor i ≃* C.factor i) : ℝ) /
            Real.logb 2 (Nat.card (C.factor i)))) *
          (1 + (b : ℝ)) ^ (2 * Fintype.card C.ι) := by
      rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
        ← pow_mul]

/-- Add one nonabelian minimal normal layer. -/
noncomputable def semisimpleStep
    {G : Type} [Group G] [Finite G]
    (E : Subgroup G) [E.Normal]
    (C : SemisimpleNormalChart E)
    (Q : FixedTargetCompositionEnvelope (G ⧸ E)) :
    FixedTargetCompositionEnvelope G where
  constant := semisimplePolynomialConstant C * Q.constant
  polynomialDegree := 2 * Fintype.card C.ι + Q.polynomialDegree
  abelianLength := Q.abelianLength
  constant_nonneg := mul_nonneg
    (semisimplePolynomialConstant_nonneg C) Q.constant_nonneg
  bound := by
    intro b J
    have houter := C.outerSum_le (J := J)
    have hpoly := semisimple_outerFactor_le_polynomial C J
    have hq := Q.bound b J
    have hweight : 0 ≤ completeQuotientWeight (R := G ⧸ E) J :=
      completeQuotientWeight_nonneg J
    have hfac : 0 ≤ C.outerFactor (Real.logb 2 (Nat.card J)) :=
      C.outerFactor_nonneg (Real.logb_nonneg (by norm_num)
        (by exact_mod_cast Nat.card_pos (α := J)))
    calc
      completeQuotientWeight (R := G) J ≤
          completeQuotientWeight (R := G ⧸ E) J *
            C.outerFactor (Real.logb 2 (Nat.card J)) := by
        simpa only [completeQuotientWeight, completeQuotientCount,
          Nat.cast_sum] using houter
      _ ≤ (Q.constant * (1 + (b : ℝ)) ^ Q.polynomialDegree *
          (2 : ℝ) ^
            ((fixedTargetCompositionGamma * Q.abelianLength) * (b : ℝ))) *
          C.outerFactor (Real.logb 2 (Nat.card J)) :=
        mul_le_mul_of_nonneg_right hq hfac
      _ ≤ (Q.constant * (1 + (b : ℝ)) ^ Q.polynomialDegree *
          (2 : ℝ) ^
            ((fixedTargetCompositionGamma * Q.abelianLength) * (b : ℝ))) *
          (semisimplePolynomialConstant C *
            (1 + (b : ℝ)) ^ (2 * Fintype.card C.ι)) :=
        mul_le_mul_of_nonneg_left hpoly
          (mul_nonneg (mul_nonneg Q.constant_nonneg (by positivity))
            (Real.rpow_nonneg (by norm_num) _))
      _ = (semisimplePolynomialConstant C * Q.constant) *
          (1 + (b : ℝ)) ^
            (2 * Fintype.card C.ι + Q.polynomialDegree) *
          (2 : ℝ) ^
            ((fixedTargetCompositionGamma * Q.abelianLength) * (b : ℝ)) := by
        rw [pow_add]
        ring

end FixedTargetCompositionEnvelope

end SymmetricSubgroupAsymptotics

end
