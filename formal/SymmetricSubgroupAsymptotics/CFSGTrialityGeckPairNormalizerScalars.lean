import SymmetricSubgroupAsymptotics.CFSGTrialityGeckDiagonalSimpleScalars
import SymmetricSubgroupAsymptotics.CFSGTrialityGeckFixedOrbitRootGroups

/-! Frobenius fixedness couples the three ambient outer scalar actions
into one cubic-field scalar. The middle scalar is literally in the
fixed field. This proves the scalar upper action of the genuine fixed
opposed-pair normalizer, without assuming it equals a generated torus. -/
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTrialityGeckPairNormalizerScalars
open CFSGTrialityD4NormTwo CFSGTrialityGeckDiagramCovariance
open CFSGTrialityGeckFixedPairNormalizer CFSGTrialityGeckDiagonalSimpleScalars
open CFSGTrialityGeckRelativeRootGenerated CFSGTrialityGeckMatrixTwist
open CFSGTrialityGeckRootSubgroupTwist CFSGTrialityGeckFixedRootWords
open CFSGTrialityGeckFixedOrbitRootGroups CFSGTrialityFixedField
open CFSGSerreDiagram CFSGSerreOrdinaryTwists CFSGSerreQuadraticMatrix
local instance : DecidableEq (CFSGNormTwoRootPairing.Roots (CartanMatrix.D 4)) := Classical.decEq _

theorem twist_simple_scalar (K : Type) [Field K] (sigma : K≃+*K)
    (d : (Matrix GeckIndex GeckIndex K)ˣ) (hdFix : unitTwist K sigma d=d)
    (i : Fin 4) (c : K)
    (hscalar : ∀t,d*canonicalRoot rawData K false i t*d⁻¹=canonicalRoot rawData K false i (c*t)) :
    ∀t,d*canonicalRoot rawData K false (trialityPermutation i) t*d⁻¹=
      canonicalRoot rawData K false (trialityPermutation i) (sigma c*t) := by
  intro t
  have hh := congrArg (unitTwist K sigma) (hscalar (sigma.symm t))
  simpa only [map_mul,map_inv,hdFix,unitTwist_raw_root,map_mul,
    RingEquiv.apply_symm_apply] using hh

theorem pairNormalizer_positive_scalars (q : CFSG.PrimePower)
    (d : (Matrix GeckIndex GeckIndex (q.Extension 3))ˣ)
    (hD : d∈pairNormalizer (q.Extension 3) (definingFieldAutomorphism q 3)) :
    ∃c:(q.Extension 3)ˣ,∃a:(fixedField q)ˣ,
      (∀t,d*shortOrbit (q.Extension 3) (definingFieldAutomorphism q 3) false t*d⁻¹=
        shortOrbit (q.Extension 3) (definingFieldAutomorphism q 3) false ((c:q.Extension 3)*t))∧
      (∀t:fixedField q,d*canonicalRoot rawData (q.Extension 3) false 1 t.val*d⁻¹=
        canonicalRoot rawData (q.Extension 3) false 1 ((a:fixedField q)*t).val) := by
  let sigma := definingFieldAutomorphism q 3
  have hfix : unitTwist (q.Extension 3) sigma d=d :=
    fixedRootGenerated_le_fixed _ _ hD.2
  obtain ⟨c,h0⟩ := pairNormalizer_simple_scalar _ sigma d hD 0
  have h02 : trialityPermutation (0:Fin 4)=2 := by decide
  have h23 : trialityPermutation (2:Fin 4)=3 := by decide
  have h11 : trialityPermutation (1:Fin 4)=1 := by decide
  have h2 : ∀t,d*canonicalRoot rawData (q.Extension 3) false 2 t*d⁻¹=
      canonicalRoot rawData (q.Extension 3) false 2 (sigma (c:q.Extension 3)*t) := by
    simpa only [h02] using twist_simple_scalar _ sigma d hfix 0 (c:q.Extension 3) h0
  have h3 : ∀t,d*canonicalRoot rawData (q.Extension 3) false 3 t*d⁻¹=
      canonicalRoot rawData (q.Extension 3) false 3 (sigma (sigma (c:q.Extension 3))*t) := by
    simpa only [h23] using twist_simple_scalar _ sigma d hfix 2 (sigma (c:q.Extension 3)) h2
  obtain ⟨b,h1⟩ := pairNormalizer_simple_scalar _ sigma d hD 1
  have h1tw : ∀t,d*canonicalRoot rawData (q.Extension 3) false 1 t*d⁻¹=
      canonicalRoot rawData (q.Extension 3) false 1 (sigma (b:q.Extension 3)*t) := by
    simpa only [h11] using twist_simple_scalar _ sigma d hfix 1 (b:q.Extension 3) h1
  have hb : sigma (b:q.Extension 3)=(b:q.Extension 3) := by
    apply canonical_middle_injective (q.Extension 3)
    simpa only [mul_one] using (h1tw 1).symm.trans (h1 1)
  let a : (fixedField q)ˣ := Units.mk0 ⟨(b:q.Extension 3),hb⟩ (by
    intro hz
    exact b.ne_zero (congrArg Subtype.val hz))
  refine ⟨c,a,?_,?_⟩
  · intro t
    calc
      _=(d*canonicalRoot rawData (q.Extension 3) false 0 t*d⁻¹)*
          (d*canonicalRoot rawData (q.Extension 3) false 2 (sigma t)*d⁻¹)*
          (d*canonicalRoot rawData (q.Extension 3) false 3 (sigma (sigma t))*d⁻¹) := by
        dsimp only [shortOrbit,sigma]
        group
      _=_ := by
        rw [h0,h2,h3]
        simp only [shortOrbit,map_mul]
        rfl
  · intro t
    exact h1 t.val

end SymmetricSubgroupAsymptotics.CFSGTrialityGeckPairNormalizerScalars
