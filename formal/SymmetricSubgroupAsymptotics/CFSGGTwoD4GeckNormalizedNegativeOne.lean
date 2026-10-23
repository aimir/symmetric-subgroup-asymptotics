import SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckOriginalSimpleStabilizer
import SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckSimpleRootRanges
import SymmetricSubgroupAsymptotics.CFSGCentralRootNegativeOneRigidity
import SymmetricSubgroupAsymptotics.CFSGTrialityGeckShortRankOneConstraint
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckRankOneConstraint

/-! Literal rank-one constraints fix the negative parameter minus one
once positive one is fixed. Central p-element separation reflects the
original quotient relation into the genuine generated matrix group. -/
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckNormalizedNegativeOne
open CFSGGTwoD4GeckOriginalSimpleParameters CFSGGTwoD4GeckSimpleParameters
open CFSGGTwoD4GeckOriginalProjection CFSGGTwoD4GeckSimpleRootRanges
open CFSGTrialityGeckRelativeRootGenerated CFSGTrialityGeckRootGeneratedPGroup
open CFSGTrialityGeckGeneratedSylow CFSGTrialityGeckOvergroupWeylExtraction
open CFSGTrialityGeckFixedRootWords CFSGTrialityGeckSimpleOrbitFlags
open CFSGTrialityGeckShortRankOneConstraint CFSGNormTwoGeckRankOneConstraint
open CFSGTrialityD4NormTwo CFSGTrialityGeckDiagramCovariance
open CFSGSerreQuadraticMatrix CFSGSerreQuadraticWeylWord CFSGCentralRootNegativeOneRigidity CFSG.Models.Chevalley
local instance : DecidableEq (CFSGNormTwoRootPairing.Roots (CartanMatrix.D 4)) := Classical.decEq _
variable (K : Type) [Field K] [Finite K]
local notation "J" => fixedRootGenerated K (RingEquiv.refl K)

def generatedWeylElement (a : Bool) : J :=
  simpleGeneratedHom K false a (Multiplicative.ofAdd 1)*
    simpleGeneratedHom K true a (Multiplicative.ofAdd (-1))*
      simpleGeneratedHom K false a (Multiplicative.ofAdd 1)

theorem generated_weyl_root_conjugation (a : Bool) (t : K) :
    generatedWeylElement K a*simpleGeneratedHom K false a (Multiplicative.ofAdd t)*
      (generatedWeylElement K a)⁻¹ = simpleGeneratedHom K true a (Multiplicative.ofAdd (-t)) := by
  apply Subtype.ext
  have hword : canonicalWord rawData K (orbitWord a) = (generatedWeylElement K a).val := by
    simpa only [generatedWeylElement,Subgroup.coe_mul,simpleGeneratedHom_val,orbitParameter] using
      orbit_word_parameter K (RingEquiv.refl K) a
  change (generatedWeylElement K a).val*(simpleGeneratedHom K false a (Multiplicative.ofAdd t)).val*
    (generatedWeylElement K a).val⁻¹ = (simpleGeneratedHom K true a (Multiplicative.ofAdd (-t))).val
  rw [←hword]
  exact simple_word_conjugates K a t

private theorem simple_p_element (p : ℕ) [Fact p.Prime] [CharP K p]
    (neg a : Bool) (t : Multiplicative K) : ∃k:ℕ,(simpleGeneratedHom K neg a t)^(p^k)=1 := by
  obtain ⟨k,hk⟩ := (rootPart_isPGroup K (RingEquiv.refl K) p neg)
    ⟨simpleGeneratedHom K neg a t,simpleGeneratedHom_mem_rootPart K neg a t⟩
  exact ⟨k,congrArg Subtype.val hk⟩

variable [IsSimpleGroup (Projective CartanMatrix.G₂ K)]
variable (p : ℕ) [Fact p.Prime] [CharP K p]
include p

theorem negative_one_fixed (f : MulAut (Projective CartanMatrix.G₂ K)) (a : Bool)
    (hrange : (originalSimpleHom K true a).range.map f.toMonoidHom = (originalSimpleHom K true a).range)
    (h1 : f (originalSimpleHom K false a (Multiplicative.ofAdd 1)) =
      originalSimpleHom K false a (Multiplicative.ofAdd 1)) :
    f (originalSimpleHom K true a (Multiplicative.ofAdd (-1))) =
      originalSimpleHom K true a (Multiplicative.ofAdd (-1)) := by
  let P := positiveSylow K (RingEquiv.refl K) p
  have hP : Function.Injective ((generatedToOriginal K).comp (P : Subgroup J).subtype) := by
    intro x y he
    apply Subtype.ext
    apply generatedToOriginal_injOn_positive K _ _ he
    · simpa only [P,positiveSylow_coe] using x.property
    · simpa only [P,positiveSylow_coe] using y.property
  apply CFSGCentralRootNegativeOneRigidity.negative_one_fixed (generatedToOriginal K) P hP
    (generatedToOriginal_kernel_le_center K) (simpleGeneratedHom K false a)
    (simpleGeneratedHom K true a) (originalSimpleHom_injective K true a)
    (simple_p_element K p false a) (simple_p_element K p true a)
    (generated_weyl_root_conjugation K a 1) _ f hrange h1
  intro b hb hinter
  have he := congrArg (fun z : J => z.val) hinter
  cases a
  · change (shortOrbit K (RingEquiv.refl K) false 1*shortOrbit K (RingEquiv.refl K) true b*
      shortOrbit K (RingEquiv.refl K) false 1)*shortOrbit K (RingEquiv.refl K) false 1 =
      shortOrbit K (RingEquiv.refl K) true b*(shortOrbit K (RingEquiv.refl K) false 1*
        shortOrbit K (RingEquiv.refl K) true b*shortOrbit K (RingEquiv.refl K) false 1) at he
    have hc := short_word_inverse_constraint K (RingEquiv.refl K) 1 b 1 b hb he
    linear_combination hc
  · change (canonicalRoot rawData K false 1 1*canonicalRoot rawData K true 1 b*
      canonicalRoot rawData K false 1 1)*canonicalRoot rawData K false 1 1 =
      canonicalRoot rawData K true 1 b*(canonicalRoot rawData K false 1 1*
        canonicalRoot rawData K true 1 b*canonicalRoot rawData K false 1 1) at he
    have hc := canonical_word_inverse_constraint (CartanMatrix.D 4) (CartanMatrix.D_transpose 4)
      D4_positive_definite Base Index K 1 1 b 1 b hb he
    linear_combination hc

end SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckNormalizedNegativeOne
