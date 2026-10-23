import SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckOriginalPairNormalizer
import SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckOriginalProductTorusAction
import SymmetricSubgroupAsymptotics.CFSGTrialityGeckPairNormalizerScalars

/-! Actual scalar upper bounds and complete scalar realization for the
same original opposed-pair normalizer. Diagram fixedness identifies the
three outer scalars; the unimodular G2 torus supplies every pair. -/
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckPairNormalizerScalars
open CFSGGTwoD4GeckOriginalPairNormalizer CFSGGTwoD4GeckOriginalProjection
open CFSGGTwoD4GeckOriginalSimpleParameters CFSGGTwoD4GeckSimpleParameters
open CFSGGTwoD4GeckOriginalProductTorusAction CFSGGTwoD4GeckProductTorusParameters
open CFSGGTwoD4GeckScalarTorus CFSGGTwoD4GeckProductTorus
open CFSGTrialityGeckPairNormalizerScalars CFSGTrialityGeckDiagonalSimpleScalars
open CFSGTrialityGeckFixedPairNormalizer CFSGTrialityGeckRelativeRootGenerated
open CFSGTrialityGeckFixedRootWords CFSGTrialityGeckDiagramCovariance
open CFSGTrialityD4NormTwo CFSGSerreQuadraticMatrix CFSG.Models.Chevalley
local instance : DecidableEq (CFSGNormTwoRootPairing.Roots (CartanMatrix.D 4)) := Classical.decEq _
variable (K : Type) [Field K] [Finite K]
local notation "J" => fixedRootGenerated K (RingEquiv.refl K)

private theorem raw_positive_scalars (d : (Matrix GeckIndex GeckIndex K)ˣ)
    (hd : d ∈ pairNormalizer K (RingEquiv.refl K)) :
    ∃ c : Bool → Kˣ, ∀ (a : Bool) (t : K),
      d * (simpleGeneratedHom K false a (Multiplicative.ofAdd t)).val * d⁻¹ =
        (simpleGeneratedHom K false a (Multiplicative.ofAdd ((c a : K)*t))).val := by
  have hfix := fixedRootGenerated_le_fixed K (RingEquiv.refl K) hd.2
  obtain ⟨c,h0⟩ := pairNormalizer_simple_scalar K (RingEquiv.refl K) d hd 0
  obtain ⟨b,h1⟩ := pairNormalizer_simple_scalar K (RingEquiv.refl K) d hd 1
  have h02 : CFSGSerreDiagram.trialityPermutation (0 : Fin 4) = 2 := by decide
  have h23 : CFSGSerreDiagram.trialityPermutation (2 : Fin 4) = 3 := by decide
  have h2 : ∀t, d*canonicalRoot rawData K false 2 t*d⁻¹ = canonicalRoot rawData K false 2 ((c:K)*t) := by
    simpa only [h02,RingEquiv.refl_apply] using
      twist_simple_scalar K (RingEquiv.refl K) d hfix 0 (c:K) h0
  have h3 : ∀t, d*canonicalRoot rawData K false 3 t*d⁻¹ = canonicalRoot rawData K false 3 ((c:K)*t) := by
    simpa only [h23,RingEquiv.refl_apply] using
      twist_simple_scalar K (RingEquiv.refl K) d hfix 2 (c:K) h2
  refine ⟨fun a => if a then b else c, ?_⟩
  intro a t
  cases a
  · simp only [simpleGeneratedHom_val,Bool.false_eq_true,if_false,shortOrbit,RingEquiv.refl_apply,toAdd_ofAdd]
    calc
      _ = (d*canonicalRoot rawData K false 0 t*d⁻¹)*
          (d*canonicalRoot rawData K false 2 t*d⁻¹)*
          (d*canonicalRoot rawData K false 3 t*d⁻¹) := by group
      _ = _ := by rw [h0,h2,h3]
  · simpa only [simpleGeneratedHom_val,if_true] using h1 t

variable [IsSimpleGroup (Projective CartanMatrix.G₂ K)]
variable (p : ℕ) [Fact p.Prime] [CharP K p]

theorem originalPairNormalizer_positive_scalars (d : Projective CartanMatrix.G₂ K)
    (hd : d ∈ originalPairNormalizer K p) :
    ∃ c : Bool → Kˣ, ∀ (a : Bool) (t : K),
      d*originalSimpleHom K false a (Multiplicative.ofAdd t)*d⁻¹ =
        originalSimpleHom K false a (Multiplicative.ofAdd ((c a : K)*t)) := by
  obtain ⟨g,rfl⟩ := generatedToOriginal_surjective K d
  obtain ⟨c,hc⟩ := raw_positive_scalars K g.val ((mem_originalPairNormalizer_iff K p g).mp hd)
  refine ⟨c,?_⟩
  intro a t
  have he : g*simpleGeneratedHom K false a (Multiplicative.ofAdd t)*g⁻¹ =
      simpleGeneratedHom K false a (Multiplicative.ofAdd ((c a : K)*t)) := Subtype.ext (hc a t)
  simpa only [map_mul,map_inv,originalSimpleHom,MonoidHom.comp_apply] using
    congrArg (generatedToOriginal K) he

theorem originalPairNormalizer_realizes_scalars (c : Bool → Kˣ) :
    ∃ d ∈ originalPairNormalizer K p, ∀ (a : Bool) (t : K),
      d*originalSimpleHom K false a (Multiplicative.ofAdd t)*d⁻¹ =
        originalSimpleHom K false a (Multiplicative.ofAdd ((c a : K)*t)) := by
  let z : Fin 2 → Kˣ := fun i => if i=0 then c false else c true
  let x := (scalarEquiv Kˣ).symm z
  have hx : CFSGIntegerMatrixPowerHom.powerHom (G:=Kˣ) relativeCartan x = z :=
    (scalarEquiv Kˣ).apply_symm_apply z
  refine ⟨originalProductTorus K x,?_,?_⟩
  · constructor
    · change originalProductTorus K x ∈ Subgroup.normalizer
        ((originalPositiveSylow K p : Subgroup (Projective CartanMatrix.G₂ K)) : Set (Projective CartanMatrix.G₂ K))
      rw [originalPositiveSylow_coe K p]
      exact originalProductTorus_normalizes K x false
    · exact originalProductTorus_normalizes K x true
  · intro a t
    have he := originalProductTorus_simple_action K x false a t
    have hs : parameterScalar K x false a = c a := by
      change CFSGIntegerMatrixPowerHom.powerHom (G:=Kˣ) relativeCartan x (if a then 1 else 0) = c a
      rw [hx]
      cases a
      · rfl
      · exact if_neg (by decide)
    rw [hs,mul_comm t] at he
    exact he

end SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckPairNormalizerScalars
