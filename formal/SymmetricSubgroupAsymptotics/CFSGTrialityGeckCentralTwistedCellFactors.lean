import SymmetricSubgroupAsymptotics.CFSGTrialityGeckEnvelopeOppositeIntersection
import SymmetricSubgroupAsymptotics.CFSGTrialityGeckNormalizerEnvelopeTwist
import SymmetricSubgroupAsymptotics.CFSGTrialityGeckEnvelopeBlocks
import SymmetricSubgroupAsymptotics.CFSGTrialityGeckFixedInversionFactors

/-! Unique inversion and positive/diagonal coordinates retain literal
fixedness for centrally twisted elements. Only the diagonal coordinate
carries the central difference. No fixed lift or torus recognition is
assumed in this calculation. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGTrialityGeckCentralTwistedCellFactors
open CFSGTrialityD4NormTwo CFSGTrialityGeckDiagramCovariance
open CFSGTrialityGeckMatrixTwist CFSGTrialityGeckPositiveTwist
open CFSGTrialityGeckNormalizerEnvelope CFSGTrialityGeckNormalizerEnvelopeTwist
open CFSGTrialityGeckEnvelopeOppositeIntersection CFSGTrialityGeckEnvelopeBlocks
open CFSGTrialityGeckBruhatCellFactors CFSGTrialityGeckFixedInversionFactors
open CFSGTrialityGeckSourceWordAction CFSGTrialityGeckAmbientPositiveSylow
open CFSGNormTwoGeckWeylWordDegree CFSGNormTwoGeckIntegralWord

private theorem twisted_product_values {G C : Type*} [Group G] [Group C]
    (tau : G →* G) (B : Subgroup G) (W z : G) (e : C →* G)
    (hinj : Function.Injective (fun p : B × C => (p.1.val : G) * W * e p.2))
    (b bt bz : B) (v vt : C) (hbt : bt.val = tau b.val) (hbz : bz.val = z * b.val)
    (hvt : e vt = tau (e v)) (hW : tau W = W)
    (htwist : tau (b.val * W * e v) = z * (b.val * W * e v)) :
    tau b.val = z * b.val ∧ tau (e v) = e v := by
  have hp : bt.val * W * e vt = bz.val * W * e v := by
    calc
      _ = tau (b.val * W * e v) := by rw [map_mul, map_mul, hW, hbt, hvt]
      _ = z * (b.val * W * e v) := htwist
      _ = _ := by rw [hbz]; simp only [mul_assoc]
  have he := hinj (a₁ := (bt, vt)) (a₂ := (bz, v)) hp
  exact ⟨hbt.symm.trans ((congrArg (fun p => p.1.val) he).trans hbz),
    hvt.symm.trans (congrArg (fun p => e p.2) he)⟩

theorem envelope_inversion_factors_injective (K : Type) [Field K] (w : List (Fin 4)) :
    Function.Injective (fun p : normalizerEnvelope K × InversionPart K w =>
      (p.1.val : (Matrix GeckIndex GeckIndex K)ˣ) *
        wordUnit (CartanMatrix.D 4) (CartanMatrix.D_transpose 4)
          D4_positive_definite Base Index K w * inversionEmbedding K w p.2) := by
  apply shifted_product_factors_injective _ (Negative K) _ _
    (inversionEmbedding_injective K w) (envelope_negative_disjoint K)
  intro v
  rw [word_eq_canonicalWord]
  exact v.property

theorem central_twisted_cell_coordinates (K : Type) [Field K] (sigma : K ≃+* K)
    (w : List (Fin 4))
    (hW : unitTwist K sigma (wordUnit (CartanMatrix.D 4) (CartanMatrix.D_transpose 4)
      D4_positive_definite Base Index K w) =
      wordUnit (CartanMatrix.D 4) (CartanMatrix.D_transpose 4)
        D4_positive_definite Base Index K w)
    (z : MatrixGroup K) (hz : z ∈ Subgroup.center (MatrixGroup K))
    (b : normalizerEnvelope K) (v : InversionPart K w)
    (htwist : unitTwist K sigma (b.val *
      wordUnit (CartanMatrix.D 4) (CartanMatrix.D_transpose 4)
        D4_positive_definite Base Index K w * inversionEmbedding K w v) =
      z.val * (b.val * wordUnit (CartanMatrix.D 4) (CartanMatrix.D_transpose 4)
        D4_positive_definite Base Index K w * inversionEmbedding K w v)) :
    unitTwist K sigma b.val = z.val * b.val ∧
      unitTwist K sigma (inversionEmbedding K w v) = inversionEmbedding K w v := by
  let bt : normalizerEnvelope K :=
    ⟨unitTwist K sigma b.val, normalizer_envelope_twist_mem K sigma b.val b.property⟩
  let bz : normalizerEnvelope K := ⟨z.val * b.val,
    (normalizerEnvelope K).mul_mem
      (diagonalNormalizer_le_envelope K (center_mem_diagonalNormalizer K z hz)) b.property⟩
  let vt := inversionTwistElement K sigma w hW v
  exact twisted_product_values (unitTwist K sigma).toMonoidHom _ _ z.val
    (inversionEmbedding K w) (envelope_inversion_factors_injective K w)
    b bt bz v vt rfl rfl (inversionTwistElement_value K sigma w hW v) hW htwist

private theorem twisted_diagonal_values {G : Type*} [Group G]
    (tau : G →* G) (U D : Subgroup G)
    (hinj : Function.Injective (fun p : U × D => (p.1.val : G) * p.2.val))
    (z : G) (u ut : U) (d dt dz : D)
    (hut : ut.val = tau u.val) (hdt : dt.val = tau d.val) (hdz : dz.val = z * d.val)
    (hcomm : Commute z u.val) (htwist : tau (u.val * d.val) = z * (u.val * d.val)) :
    tau u.val = u.val ∧ tau d.val = z * d.val := by
  have hp : ut.val * dt.val = u.val * dz.val := by
    calc
      _ = tau (u.val * d.val) := by rw [map_mul, hut, hdt]
      _ = z * (u.val * d.val) := htwist
      _ = _ := by rw [← mul_assoc, hcomm.eq, mul_assoc, hdz]
  have he := hinj (a₁ := (ut, dt)) (a₂ := (u, dz)) hp
  exact ⟨hut.symm.trans (congrArg (fun p => p.1.val) he),
    hdt.symm.trans ((congrArg (fun p => p.2.val) he).trans hdz)⟩

theorem exists_central_twisted_envelope_factors (K : Type) [Field K] (sigma : K ≃+* K)
    (b : (Matrix GeckIndex GeckIndex K)ˣ) (hb : b ∈ normalizerEnvelope K)
    (z : MatrixGroup K) (hz : z ∈ Subgroup.center (MatrixGroup K))
    (htwist : unitTwist K sigma b = z.val * b) :
    ∃ u ∈ Positive K, unitTwist K sigma u = u ∧
      ∃ d ∈ diagonalNormalizer K, unitTwist K sigma d = z.val * d ∧ b = u * d := by
  obtain ⟨u, hu, d, hd, _, he⟩ := normalizer_envelope_factor K b hb
  have htu : unitTwist K sigma u ∈ Positive K := by
    have hm : unitTwist K sigma u ∈ (Positive K).map (unitTwist K sigma).toMonoidHom :=
      ⟨u, hu, rfl⟩
    rwa [positive_twist_map] at hm
  let ut : Positive K := ⟨unitTwist K sigma u, htu⟩
  let dt : diagonalNormalizer K :=
    ⟨unitTwist K sigma d, diagonalNormalizer_twist_mem K sigma d hd⟩
  let dz : diagonalNormalizer K :=
    ⟨z.val * d, (diagonalNormalizer K).mul_mem (center_mem_diagonalNormalizer K z hz) hd⟩
  have hc : Commute z.val u := by
    have hh := congrArg (fun a : MatrixGroup K => a.val)
      (Subgroup.mem_center_iff.mp hz ⟨u, positive_le_matrixGroup K hu⟩)
    exact hh.symm
  have htw : unitTwist K sigma (u * d) = z.val * (u * d) := by rwa [← he]
  have hh := twisted_diagonal_values (unitTwist K sigma).toMonoidHom
    (Positive K) (diagonalNormalizer K) (positive_diagonalNormalizer_factors_injective K)
    z.val ⟨u, hu⟩ ut ⟨d, hd⟩ dt dz rfl rfl rfl hc htw
  exact ⟨u, hu, hh.1, d, hd, hh.2, he⟩

end SymmetricSubgroupAsymptotics.CFSGTrialityGeckCentralTwistedCellFactors
