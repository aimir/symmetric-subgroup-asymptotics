import SymmetricSubgroupAsymptotics.CFSGTrialityGeckBruhatCellFactors
import SymmetricSubgroupAsymptotics.CFSGTrialityGeckBorelTwist

/-! Actual inversion parts of a fixed Weyl word are twist-stable.
Consequently the unique Borel/inversion coordinates of a fixed element
are fixed themselves. No fixed-point lifting or Lang theorem is used. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGTrialityGeckFixedInversionFactors
open CFSGTrialityD4NormTwo CFSGTrialityGeckDiagramCovariance
open CFSGTrialityGeckMatrixTwist CFSGTrialityGeckPositiveTwist
open CFSGTrialityGeckRootSubgroupTwist CFSGTrialityGeckBorelTwist
open CFSGTrialityGeckBruhatCellFactors CFSGNormTwoGeckBorelEnvelope
open CFSGNormTwoGeckPositivePGroup CFSGNormTwoCoordinateRootHeightQuotient
open CFSGNormTwoGeckWeylWordDegree CFSGNormTwoGeckIntegralWord
open CFSGSerreQuadraticMatrix CFSGSerreQuadraticWeylWord CFSGSerreDiagram

theorem unitTwist_negative_mem (K : Type) [Field K] (sigma : K ≃+* K)
    (v : (Matrix GeckIndex GeckIndex K)ˣ)
    (hv : v ∈ rootGroup (CartanMatrix.D 4) (CartanMatrix.D_transpose 4)
      D4_positive_definite Base Index K true) :
    unitTwist K sigma v ∈ rootGroup (CartanMatrix.D 4) (CartanMatrix.D_transpose 4)
      D4_positive_definite Base Index K true := by
  let V := rootGroup (CartanMatrix.D 4) (CartanMatrix.D_transpose 4)
    D4_positive_definite Base Index K true
  have hle : V ≤ V.comap (unitTwist K sigma).toMonoidHom := by
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨⟨i, a⟩, rfl⟩
    change unitTwist K sigma (canonicalRoot rawData K true i a) ∈ V
    rw [unitTwist_raw_root]
    exact Subgroup.subset_closure ⟨(trialityPermutation i, sigma a), rfl⟩
  exact hle hv

def inversionTwistElement (K : Type) [Field K] (sigma : K ≃+* K)
    (w : List (Fin 4))
    (hW : unitTwist K sigma (wordUnit (CartanMatrix.D 4) (CartanMatrix.D_transpose 4)
      D4_positive_definite Base Index K w) =
      wordUnit (CartanMatrix.D 4) (CartanMatrix.D_transpose 4)
        D4_positive_definite Base Index K w)
    (v : InversionPart K w) : InversionPart K w := by
  have hp : unitTwist K sigma v.val.val ∈ Positive K := by
    have hm : unitTwist K sigma v.val.val ∈ (Positive K).map (unitTwist K sigma).toMonoidHom :=
      ⟨v.val.val, v.val.property, rfl⟩
    rwa [positive_twist_map] at hm
  refine ⟨⟨unitTwist K sigma v.val.val, hp⟩, ?_⟩
  change MulAut.conj (canonicalWord rawData K w) (unitTwist K sigma v.val.val) ∈
    rootGroup (CartanMatrix.D 4) (CartanMatrix.D_transpose 4)
      D4_positive_definite Base Index K true
  have hw : unitTwist K sigma (canonicalWord rawData K w) = canonicalWord rawData K w := by
    simpa only [word_eq_canonicalWord] using hW
  have hn : unitTwist K sigma (MulAut.conj (canonicalWord rawData K w) v.val.val) ∈
      rootGroup (CartanMatrix.D 4) (CartanMatrix.D_transpose 4)
        D4_positive_definite Base Index K true :=
    unitTwist_negative_mem K sigma _ v.property
  have he : unitTwist K sigma (MulAut.conj (canonicalWord rawData K w) v.val.val) =
      MulAut.conj (canonicalWord rawData K w) (unitTwist K sigma v.val.val) := by
    change unitTwist K sigma (_ * _ * _⁻¹) = _ * _ * _⁻¹
    rw [map_mul, map_mul, map_inv, hw]
  rwa [he] at hn

theorem inversionTwistElement_value (K : Type) [Field K] (sigma : K ≃+* K)
    (w : List (Fin 4)) (hW) (v : InversionPart K w) :
    inversionEmbedding K w (inversionTwistElement K sigma w hW v) =
      unitTwist K sigma (inversionEmbedding K w v) := rfl

private theorem fixed_factor_values {G C : Type*} [Group G] [Group C]
    (tau : G →* G) (B : Subgroup G) (W : G) (e : C →* G)
    (hinj : Function.Injective (fun p : B × C => (p.1.val : G) * W * e p.2))
    (b b' : B) (v v' : C) (hb : b'.val = tau b.val) (hv : e v' = tau (e v))
    (hW : tau W = W) (hfixed : tau (b.val * W * e v) = b.val * W * e v) :
    tau b.val = b.val ∧ tau (e v) = e v := by
  have hp : b'.val * W * e v' = b.val * W * e v := by
    calc
      _ = tau (b.val * W * e v) := by rw [map_mul, map_mul, hW, hb, hv]
      _ = _ := hfixed
  have he := hinj (a₁ := (b', v')) (a₂ := (b, v)) hp
  exact ⟨hb.symm.trans (congrArg (fun p => p.1.val) he),
    hv.symm.trans (congrArg (fun p => e p.2) he)⟩

theorem fixed_cell_factors (K : Type) [Field K] (sigma : K ≃+* K)
    (w : List (Fin 4))
    (hW : unitTwist K sigma (wordUnit (CartanMatrix.D 4) (CartanMatrix.D_transpose 4)
      D4_positive_definite Base Index K w) =
      wordUnit (CartanMatrix.D 4) (CartanMatrix.D_transpose 4)
        D4_positive_definite Base Index K w)
    (b : borelEnvelope (CartanMatrix.D 4) (CartanMatrix.D_transpose 4)
      D4_positive_definite Base Index K) (v : InversionPart K w)
    (hfixed : unitTwist K sigma (b.val *
      wordUnit (CartanMatrix.D 4) (CartanMatrix.D_transpose 4)
        D4_positive_definite Base Index K w * inversionEmbedding K w v) =
      b.val * wordUnit (CartanMatrix.D 4) (CartanMatrix.D_transpose 4)
        D4_positive_definite Base Index K w * inversionEmbedding K w v) :
    unitTwist K sigma b.val = b.val ∧
      unitTwist K sigma (inversionEmbedding K w v) = inversionEmbedding K w v := by
  let b' : borelEnvelope (CartanMatrix.D 4) (CartanMatrix.D_transpose 4)
      D4_positive_definite Base Index K :=
    ⟨unitTwist K sigma b.val, unitTwist_borel_mem K sigma b.val b.property⟩
  let v' := inversionTwistElement K sigma w hW v
  exact fixed_factor_values (unitTwist K sigma).toMonoidHom _ _
    (inversionEmbedding K w) (borel_inversion_factors_injective K w) b b' v v'
    rfl (inversionTwistElement_value K sigma w hW v) hW hfixed

end SymmetricSubgroupAsymptotics.CFSGTrialityGeckFixedInversionFactors
