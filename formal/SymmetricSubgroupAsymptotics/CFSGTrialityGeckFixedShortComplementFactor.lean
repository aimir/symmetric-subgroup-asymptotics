import SymmetricSubgroupAsymptotics.CFSGTrialityGeckOuterParameterChart
import SymmetricSubgroupAsymptotics.CFSGTrialityGeckShortComplementFixedFactor

/-! A genuinely fixed positive element factors through one actual short
orbit root and a genuinely fixed short complement. The outer parameters
are proved to be a Frobenius triple by the actual leading-coordinate
chart; no orbit-parameter or fixed-lifting premise is retained. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGTrialityGeckFixedShortComplementFactor
open CFSGTrialityGeckOuterParameterChart CFSGTrialityGeckShortComplementFixedFactor
open CFSGTrialityGeckShortComplementFactor CFSGTrialityGeckShortComplement
open CFSGTrialityGeckFixedRootWords CFSGTrialityGeckShortParameterWeyl
open CFSGTrialityGeckMatrixTwist CFSGTrialityGeckRootSubgroupTwist
open CFSGTrialityGeckDiagramCovariance CFSGTrialityGeckPositiveTwist CFSGSerreQuadraticMatrix

def outerTwistedParameters (K : Type) [Field K] (σ : K ≃+* K)
    (a : Fin 3 → Multiplicative K) : Fin 3 → Multiplicative K :=
  ![Multiplicative.ofAdd (σ (a 2).toAdd), Multiplicative.ofAdd (σ (a 0).toAdd),
    Multiplicative.ofAdd (σ (a 1).toAdd)]

theorem outerProductHom_twist (K : Type) [Field K] (σ : K ≃+* K)
    (a : Fin 3 → Multiplicative K) :
    unitTwist K σ (outerProductHom K a) = outerProductHom K (outerTwistedParameters K σ a) := by
  rw [outerProductHom_explicit, map_mul, map_mul, unitTwist_raw_root,
    unitTwist_raw_root, unitTwist_raw_root, outerProductHom_explicit]
  change canonicalRoot rawData K false 2 (σ (a 0).toAdd) *
    canonicalRoot rawData K false 3 (σ (a 1).toAdd) *
    canonicalRoot rawData K false 0 (σ (a 2).toAdd) =
      canonicalRoot rawData K false 0 (σ (a 2).toAdd) *
        canonicalRoot rawData K false 2 (σ (a 0).toAdd) *
        canonicalRoot rawData K false 3 (σ (a 1).toAdd)
  have hc2 := CFSGTrialityGeckShortParameterWeyl.outer_roots_commute K 0 1 (by decide)
    false false (σ (a 2).toAdd) (σ (a 0).toAdd)
  have hc3 := CFSGTrialityGeckShortParameterWeyl.outer_roots_commute K 0 2 (by decide)
    false false (σ (a 2).toAdd) (σ (a 1).toAdd)
  simpa only [mul_assoc] using (hc2.mul_right hc3).eq.symm

theorem exists_short_orbit_of_outer_fixed (K : Type) [Field K] (σ : K ≃+* K)
    (o : (Matrix GeckIndex GeckIndex K)ˣ) (ho : o ∈ outerGroup K)
    (hfix : unitTwist K σ o = o) :
    ∃ t : K, σ (σ (σ t)) = t ∧ o = shortOrbit K σ false t := by
  obtain ⟨a, ha⟩ := ho
  rw [← ha, outerProductHom_twist] at hfix
  have hab := outerProductHom_injective K hfix
  have h0 := congrArg (fun c : Fin 3 → Multiplicative K => (c 0).toAdd) hab
  have h1 := congrArg (fun c : Fin 3 → Multiplicative K => (c 1).toAdd) hab
  have h2 := congrArg (fun c : Fin 3 → Multiplicative K => (c 2).toAdd) hab
  change σ (a 2).toAdd = (a 0).toAdd at h0
  change σ (a 0).toAdd = (a 1).toAdd at h1
  change σ (a 1).toAdd = (a 2).toAdd at h2
  refine ⟨(a 0).toAdd, ?_, ?_⟩
  · rw [h1, h2, h0]
  · rw [← ha, outerProductHom_explicit]
    simp only [shortOrbit, h1, h2]

theorem exists_fixed_positive_short_factor (K : Type) [Field K] (σ : K ≃+* K)
    (u : (Matrix GeckIndex GeckIndex K)ˣ) (hu : u ∈ Positive K)
    (hfix : unitTwist K σ u = u) :
    ∃ c ∈ shortComplement K, ∃ t : K,
      unitTwist K σ c = c ∧ σ (σ (σ t)) = t ∧ u = c * shortOrbit K σ false t := by
  obtain ⟨c, hc, o, ho, hcfix, hofix, he⟩ := exists_fixed_short_factors K σ u hu hfix
  obtain ⟨t, ht, hot⟩ := exists_short_orbit_of_outer_fixed K σ o ho hofix
  exact ⟨c, hc, t, hcfix, ht, he.trans (congrArg (fun x => c * x) hot)⟩

end SymmetricSubgroupAsymptotics.CFSGTrialityGeckFixedShortComplementFactor
