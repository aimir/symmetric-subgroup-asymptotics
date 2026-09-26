import SymmetricSubgroupAsymptotics.BinaryCarrierReservePrefactor
import SymmetricSubgroupAsymptotics.BinaryCarrierWordProductEnergy
import SymmetricSubgroupAsymptotics.BinaryMixtureNumerics

/-! A finite logarithmic envelope for the actual terminal carrier reserve.
The enormous structured order constant is kept symbolic. Every polynomial,
normal-history multiplicity, Euler factor and relation term is included.
-/
set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics.BinaryCarrierReserveEnvelope

open BinaryCarrierWord

/-- Depends only on the fixed carrier order cap, never on a profile. -/
def constant (b : ℕ) : ℝ :=
  BinaryCarrierReservePrefactor.logConstant b (binaryStructuredOrderConstant b)
    (2^b) ((eulerProduct⁻¹)^3) / Real.log 2

theorem constant_nonneg (b : ℕ) : 0 ≤ constant b :=
  div_nonneg (BinaryCarrierReservePrefactor.logConstant_nonneg _ _ _ _)
    (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le

/-- The complete actual reserve has the required fixed-order envelope at
every total half-degree at least one. Only the structural occurrence bound
L≤T is supplied; no weighted-count or asymptotic premise appears. -/
theorem terminalProductReserve_le (b : ℕ) {ι : Type} [Fintype ι]
    (a : ℕ) (s : ι → Bool) (L : ℕ) (T : ℝ)
    (hT : 0 ≤ T) (hL : (L : ℝ) ≤ T)
    (hN : 1 ≤ (criticalProductRank a s : ℝ)+4*T) :
    terminalProductReserve a s b L T ≤
      (2 : ℝ)^(((criticalProductRank a s : ℝ)+4*T)^2/4 -
        (29/656)*T*((criticalProductRank a s : ℝ)+4*T) +
          constant b*((criticalProductRank a s : ℝ)+4*T)*
            Real.log ((criticalProductRank a s : ℝ)+4*T+2)) := by
  let R : ℕ := criticalProductRank a s
  let N : ℝ := (R : ℝ)+4*T
  have hR0 : (0 : ℝ) ≤ R := Nat.cast_nonneg R
  have hRN : (R : ℝ) ≤ N := by dsimp [N]; linarith
  have hcR : (Fintype.card ι : ℝ) ≤ R := by
    have h := terminalCritical_two_card_le_rank a s
    have hn : Fintype.card ι ≤ R := by dsimp [R]; omega
    exact_mod_cast hn
  have hLN : (L : ℝ) ≤ N := by dsimp [N]; linarith
  have hp := BinaryCarrierReservePrefactor.value_le b
    (binaryStructuredOrderConstant b) (2^b) R (Fintype.card ι) L
    ((eulerProduct⁻¹)^3) N (binaryStructuredOrderConstant_pos b)
    (by positivity [euler_positive]) hN hRN (hcR.trans hRN) hLN
  change BinaryCarrierReservePrefactor.value b
    (binaryStructuredOrderConstant b) (2^b) R (Fintype.card ι) L
    ((eulerProduct⁻¹)^3) ≤ (2 : ℝ)^(constant b*N*Real.log (N+2)) at hp
  have hquad := BinaryMixtureNumerics.carrier_reserve_le_linear (R : ℝ) T hR0 hT
  calc
    terminalProductReserve a s b L T =
        BinaryCarrierReservePrefactor.value b (binaryStructuredOrderConstant b)
          (2^b) R (Fintype.card ι) L ((eulerProduct⁻¹)^3) *
            (2 : ℝ)^(N^2/4-(25/82)*(R : ℝ)*T-(29/164)*T^2) := by
      unfold terminalProductReserve BinaryCarrierReservePrefactor.value
      dsimp [R, N]
      push_cast
      ring
    _ ≤ (2 : ℝ)^(constant b*N*Real.log (N+2)) *
        (2 : ℝ)^(N^2/4-(25/82)*(R : ℝ)*T-(29/164)*T^2) :=
      mul_le_mul_of_nonneg_right hp (by positivity)
    _ = (2 : ℝ)^(N^2/4-(25/82)*(R : ℝ)*T-(29/164)*T^2+
        constant b*N*Real.log (N+2)) := by
      rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      congr 1
      ring
    _ ≤ _ := by
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      change N^2/4-(25/82)*(R : ℝ)*T-(29/164)*T^2+
        constant b*N*Real.log (N+2) ≤
          N^2/4-(29/656)*T*N+constant b*N*Real.log (N+2)
      exact add_le_add hquad le_rfl

/-- Existence form for consumers that need only a fixed logarithmic cost.
The witness is the explicit constant above and is independent of ι. -/
theorem exists_terminalProductReserve_envelope (b : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {ι : Type} [Fintype ι]
      (a : ℕ) (s : ι → Bool) (L : ℕ) (T : ℝ),
      0 ≤ T → (L : ℝ) ≤ T → 1 ≤ (criticalProductRank a s : ℝ)+4*T →
      terminalProductReserve a s b L T ≤
        (2 : ℝ)^(((criticalProductRank a s : ℝ)+4*T)^2/4 -
          (29/656)*T*((criticalProductRank a s : ℝ)+4*T) +
            K*((criticalProductRank a s : ℝ)+4*T)*
              Real.log ((criticalProductRank a s : ℝ)+4*T+2)) := by
  refine ⟨constant b, constant_nonneg b, ?_⟩
  intro ι _ a s L T hT hL hN
  exact terminalProductReserve_le b a s L T hT hL hN

end SymmetricSubgroupAsymptotics.BinaryCarrierReserveEnvelope
