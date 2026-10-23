import SymmetricSubgroupAsymptotics.CFSGTrialityGeckPositiveActionInjective
import SymmetricSubgroupAsymptotics.CFSGTrialityGeckLongA2Commutator
import SymmetricSubgroupAsymptotics.CFSGTrialityGeckSectionQuotientCoordinates
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckOppositeIntersection
import Mathlib.Tactic.Group

/-! The actual fixed positive long sections give two noncommuting
actions on the SAME integral Geck image. Their coefficient-one A2
commutator is a conjugate of the parameter-one central simple root.
The statement is uniform in every defining characteristic. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical commutatorElement
namespace SymmetricSubgroupAsymptotics.CFSGTrialityGeckFixedPositiveNoncommute
open CFSGTrialityD4NormTwo CFSGTrialityGeckDiagramCovariance
open CFSGTrialityGeckSourceWordAction CFSGTrialityGeckPositiveTwist
open CFSGTrialityGeckPositiveActionInjective CFSGTrialityGeckLongA2Commutator
open CFSGTrialityGeckSectionQuotientCoordinates CFSGTrialityGeckFixedRootSections
open CFSGSerreQuadraticMatrix CFSGNormTwoCoordinateHeight

theorem longSection_one_ne_one (K : Type) [Field K] (s : Fin 3) :
    longSection K s false 1 ≠ 1 := by
  intro h
  have he : canonicalRoot rawData K false 1 1 =
      (longTransport K s)⁻¹ * longSection K s false 1 * longTransport K s := by
    dsimp only [longSection]
    group
  rw [h, mul_one, inv_mul_cancel] at he
  exact CFSGNormTwoGeckOppositeIntersection.canonicalRoot_one_ne_one
    (CartanMatrix.D 4) (CartanMatrix.D_transpose 4) D4_positive_definite Base Index
    coordinateHeight (simple_height (CartanMatrix.D 4) (CartanMatrix.D_diag 4)
      (CartanMatrix.D_transpose 4) D4_positive_definite (CartanMatrix.D_off_diag_nonpos 4)) K 1 he

theorem exists_fixed_positive_noncommuting_actions (K : Type) [Field K] [Finite K]
    (σ : K ≃+* K) (p : ℕ) [Fact p.Prime] [CharP K p] :
    ∃ u v : Positive K, positiveTwist K σ u = u ∧ positiveTwist K σ v = v ∧
      ¬ Commute (positiveAction K u) (positiveAction K v) := by
  obtain ⟨ε, hε, hcomm⟩ := long_commutator_sign
  let u := longPositiveSection K 0 (Multiplicative.ofAdd (ε : K))
  let v := longPositiveSection K 1 (Multiplicative.ofAdd (1 : K))
  have hu : positiveTwist K σ u = u :=
    longPositiveSection_fixed K σ 0 (Multiplicative.ofAdd (ε : K)) (map_intCast σ ε)
  have hv : positiveTwist K σ v = v :=
    longPositiveSection_fixed K σ 1 (Multiplicative.ofAdd (1 : K)) (map_one σ)
  have hcoeff : (ε : K) * ((ε : K) * 1) = 1 := by
    rcases hε with rfl | rfl <;> simp
  have he : ⁅u, v⁆ = longPositiveSection K 2 (Multiplicative.ofAdd (1 : K)) := by
    apply Subtype.ext
    change longSection K 0 false (ε : K) * longSection K 1 false 1 *
      (longSection K 0 false (ε : K))⁻¹ * (longSection K 1 false 1)⁻¹ =
        longSection K 2 false 1
    exact (hcomm K (ε : K) 1).trans (congrArg (longSection K 2 false) hcoeff)
  refine ⟨u, v, hu, hv, ?_⟩
  intro hc
  have hact : positiveAction K ⁅u, v⁆ = positiveAction K 1 := by
    rw [map_commutatorElement, map_one]
    exact commutatorElement_eq_one_iff_mul_comm.mpr hc.eq
  have hzero := positiveAction_injective K p hact
  rw [he] at hzero
  have hh := congrArg (fun x : Positive K => x.val) hzero
  change longSection K 2 false 1 = 1 at hh
  exact longSection_one_ne_one K 2 hh

end SymmetricSubgroupAsymptotics.CFSGTrialityGeckFixedPositiveNoncommute
