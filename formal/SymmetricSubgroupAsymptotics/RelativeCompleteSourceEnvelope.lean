import SymmetricSubgroupAsymptotics.JointElementaryLayerEnvelope
import SymmetricSubgroupAsymptotics.MinimalNormalCompositionCharts
import SymmetricSubgroupAsymptotics.SemisimpleOuterFibre

/-!
# Relative complete-source envelopes

This file iterates elementary and semisimple normal layers while leaving one
literal quotient comparator at the end.  Unlike the fixed-target composition
envelope, the endpoint is not forced to be trivial.  Consequently an actual
imprimitive block calculation can eliminate its whole component kernel and
retain the faithful action on the real blocks.

Every constructor bounds `completeQuotientWeight`, the sum over all original
normal subgroups.  The same source subgroup `J` remains in every factor.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics

/-- A complete quotient-weight transfer from `G` to one faithfully acting
finite comparator. -/
structure RelativeCompleteSourceEnvelope
    (G : Type) [Group G] [Finite G] where
  R : Type
  [groupR : Group R]
  [finiteR : Finite R]
  v : ℕ
  action : R →* Equiv.Perm (Fin v)
  action_injective : Function.Injective action
  coefficient : ℕ → ℝ
  eta : ℝ
  coefficient_nonneg : ∀ b, 0 ≤ coefficient b
  bound : ∀ b (J : Subgroup (Equiv.Perm (Fin b))),
    completeQuotientWeight (R := G) J ≤
      coefficient b * (2 : ℝ) ^ (eta * b) *
        completeQuotientWeight (R := R) J

attribute [instance]
  RelativeCompleteSourceEnvelope.groupR
  RelativeCompleteSourceEnvelope.finiteR

namespace RelativeCompleteSourceEnvelope

/-- Stop the relative induction at any literal faithful comparator. -/
def identity
    (G : Type) [Group G] [Finite G]
    (v : ℕ) (action : G →* Equiv.Perm (Fin v))
    (haction : Function.Injective action) :
    RelativeCompleteSourceEnvelope G where
  R := G
  groupR := inferInstance
  finiteR := inferInstance
  v := v
  action := action
  action_injective := haction
  coefficient := fun _ ↦ 1
  eta := 0
  coefficient_nonneg := fun _ ↦ by norm_num
  bound := by
    intro b J
    simp

private theorem rpow_eq_two_rpow_logb
    {B : ℝ} (hB : 0 < B) (x : ℝ) :
    B ^ x = (2 : ℝ) ^ (Real.logb 2 B * x) := by
  rw [Real.rpow_mul (by norm_num),
    Real.rpow_logb (by norm_num) (by norm_num) hB]

/-- Add one elementary normal layer, with the section capacity supplied on
the literal layer. -/
noncomputable def elementaryStep
    {p : ℕ} [Fact p.Prime]
    {G : Type} [Group G] [Finite G]
    (E : Subgroup G) [E.Normal]
    (C : ElementaryMinimalNormalChart E)
    [Finite C.quotientRepresentation]
    (H : ElementaryLayerJointCapacityBound C.p
      (QuotientGroup.mk' E) (QuotientGroup.mk'_surjective E)
        C.quotientRepresentation C.originalKernelChart)
    (Q : RelativeCompleteSourceEnvelope (G ⧸ E)) :
    RelativeCompleteSourceEnvelope G where
  R := Q.R
  groupR := Q.groupR
  finiteR := Q.finiteR
  v := Q.v
  action := Q.action
  action_injective := Q.action_injective
  coefficient := fun b ↦
    H.coefficient * Q.coefficient b
  eta := Real.logb 2 C.p / C.p * H.capacity + Q.eta
  coefficient_nonneg := fun b ↦ mul_nonneg
    H.coefficient_nonneg
    (Q.coefficient_nonneg b)
  bound := by
    intro b J
    let L := H.coefficient
    have hlayer := H.completeQuotientWeight_le C.p
      (QuotientGroup.mk' E) (QuotientGroup.mk'_surjective E)
      C.quotientRepresentation C.originalKernelChart J
    have hq := Q.bound b J
    have hp0 : (0 : ℝ) < C.p := by exact_mod_cast C.p_prime.pos
    have hpow :
        (C.p : ℝ) ^ (H.capacity * ((b : ℝ) / C.p)) =
          (2 : ℝ) ^
            ((Real.logb 2 C.p / C.p * H.capacity) * (b : ℝ)) := by
      rw [rpow_eq_two_rpow_logb hp0]
      congr 1
      field_simp
    calc
      completeQuotientWeight (R := G) J ≤
          L * (C.p : ℝ) ^ (H.capacity * ((b : ℝ) / C.p)) *
            completeQuotientWeight (R := G ⧸ E) J := by
              simpa only [L] using hlayer
      _ ≤ L * (C.p : ℝ) ^ (H.capacity * ((b : ℝ) / C.p)) *
          (Q.coefficient b * (2 : ℝ) ^ (Q.eta * b) *
            completeQuotientWeight (R := Q.R) J) :=
        mul_le_mul_of_nonneg_left hq
          (mul_nonneg
            H.coefficient_nonneg
            (Real.rpow_nonneg (by positivity) _))
      _ = (L * Q.coefficient b) *
          (2 : ℝ) ^
            ((Real.logb 2 C.p / C.p * H.capacity + Q.eta) * b) *
          completeQuotientWeight (R := Q.R) J := by
        rw [hpow, show
          (Real.logb 2 C.p / C.p * H.capacity + Q.eta) * (b : ℝ) =
            (Real.logb 2 C.p / C.p * H.capacity) * b + Q.eta * b by ring,
          Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
        ring

/-- Add one semisimple normal layer.  Its exact outer factor is bounded at
`|S_b|`; no simple factor is assigned an auxiliary permutation degree. -/
noncomputable def semisimpleStep
    {G : Type} [Group G] [Finite G]
    (E : Subgroup G) [E.Normal]
    (C : SemisimpleNormalChart E)
    (Q : RelativeCompleteSourceEnvelope (G ⧸ E)) :
    RelativeCompleteSourceEnvelope G where
  R := Q.R
  groupR := Q.groupR
  finiteR := Q.finiteR
  v := Q.v
  action := Q.action
  action_injective := Q.action_injective
  coefficient := fun b ↦
    C.outerFactor (Real.logb 2 (Nat.factorial b)) * Q.coefficient b
  eta := Q.eta
  coefficient_nonneg := fun b ↦ mul_nonneg
    (C.outerFactor_nonneg (Real.logb_nonneg (by norm_num)
      (by exact_mod_cast Nat.factorial_pos b)))
    (Q.coefficient_nonneg b)
  bound := by
    intro b J
    have houter := C.outerSum_le (J := J)
    have hq := Q.bound b J
    have hweight : 0 ≤ completeQuotientWeight (R := G ⧸ E) J :=
      completeQuotientWeight_nonneg J
    have hfactor0 :
        0 ≤ C.outerFactor (Real.logb 2 (Nat.card J)) :=
      C.outerFactor_nonneg (Real.logb_nonneg (by norm_num)
        (by exact_mod_cast Nat.card_pos))
    have hcard : Nat.card J ≤ Nat.factorial b := by
      have h := Nat.card_le_card_of_injective
        (Subtype.val : J → Equiv.Perm (Fin b)) Subtype.val_injective
      simpa only [Nat.card_perm, Nat.card_fin] using h
    have hlog :
        Real.logb 2 (Nat.card J) ≤ Real.logb 2 (Nat.factorial b) :=
      Real.logb_le_logb_of_le (by norm_num)
        (by exact_mod_cast Nat.card_pos) (by exact_mod_cast hcard)
    have hfactor :
        C.outerFactor (Real.logb 2 (Nat.card J)) ≤
          C.outerFactor (Real.logb 2 (Nat.factorial b)) := by
      unfold SemisimpleNormalChart.outerFactor
      apply Finset.prod_le_prod
      · intro i _
        exact add_nonneg zero_le_one
          (C.factorWeight_nonneg
            (Real.logb_nonneg (by norm_num)
              (by exact_mod_cast Nat.card_pos)) i)
      · intro i _
        simpa only [add_comm] using
          add_le_add_left (C.factorWeight_mono hlog i) 1
    calc
      completeQuotientWeight (R := G) J ≤
          completeQuotientWeight (R := G ⧸ E) J *
            C.outerFactor (Real.logb 2 (Nat.card J)) := by
        simpa only [completeQuotientWeight, completeQuotientCount,
          Nat.cast_sum] using houter
      _ ≤ (Q.coefficient b * (2 : ℝ) ^ (Q.eta * b) *
          completeQuotientWeight (R := Q.R) J) *
            C.outerFactor (Real.logb 2 (Nat.card J)) :=
        mul_le_mul_of_nonneg_right hq hfactor0
      _ ≤ (Q.coefficient b * (2 : ℝ) ^ (Q.eta * b) *
          completeQuotientWeight (R := Q.R) J) *
            C.outerFactor (Real.logb 2 (Nat.factorial b)) :=
        mul_le_mul_of_nonneg_left hfactor
          (mul_nonneg
            (mul_nonneg (Q.coefficient_nonneg b)
              (Real.rpow_nonneg (by norm_num) _))
            (completeQuotientWeight_nonneg J))
      _ = (C.outerFactor (Real.logb 2 (Nat.factorial b)) *
            Q.coefficient b) *
          (2 : ℝ) ^ (Q.eta * b) *
            completeQuotientWeight (R := Q.R) J := by ring

end RelativeCompleteSourceEnvelope
end SymmetricSubgroupAsymptotics

end
