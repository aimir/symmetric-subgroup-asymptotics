import SymmetricSubgroupAsymptotics.CFSGGTwoOriginalLongGauss
import SymmetricSubgroupAsymptotics.CFSGGTwoOriginalExceptionalModel
import SymmetricSubgroupAsymptotics.CFSGGTwoOriginalBorel

/-! The actual two rank-one Gauss factors in the SAME original Model.
The short-axis identity is the image of the long-axis identity under the
proved exceptional automorphism. No field-parameter surjectivity or
ordinary G2 simplicity is used. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGGTwoOriginalSimpleGauss
open CFSG.Models.Chevalley CFSGSerreModelRootGeneration
open CFSGGTwoOriginalRankTwoTorus CFSGGTwoOriginalLongGauss
open CFSGGTwoOriginalExceptionalModel CFSGGTwoOriginalExceptionalRootCovariance
open CFSGGTwoOriginalBorel CFSGGTwoOriginalPositiveRootWords
open CFSGGTwoPositiveCoordinateKernels CFSGGTwoSimpleBruhatComplement
open CFSGGTwoPositiveWordSubgroup
variable (K : Type) [Field K] [Finite K] [CharP K 3]
local notation "A" => CartanMatrix.G₂

theorem exceptional_longParameter (c : Kˣ) :
    exceptionalModelEquiv K (weylParameter K 1 c)=weylParameter K 0 c := by
  simp only [weylParameter,map_mul,exceptionalModelEquiv_root]
  rfl

theorem exceptional_longNode (c : Kˣ) :
    exceptionalModelEquiv K (torusNode K 1 c)=torusNode K 0 c := by
  simp only [torusNode,map_mul,exceptional_longParameter]

theorem shortParameter_gauss (c a : Kˣ) :
    weylParameter K 0 c * modelRoot A K false 0 (a:K) =
      modelRoot A K false 0 (-(c:K)^2*(a⁻¹:Kˣ)) *
        torusNode K 0 (-c*a⁻¹) * modelRoot A K true 0 (a⁻¹:Kˣ) := by
  have he := congrArg (exceptionalModelEquiv K) (longParameter_gauss K c a)
  have h10 : (1:Fin 2)≠0 := by decide
  simpa only [map_mul,exceptional_longParameter,exceptional_longNode,
    exceptionalModelEquiv_root,exchangedNode,exceptionalParameter,if_neg h10]
    using he

theorem shortWord_gauss (a : Kˣ) :
    shortWord K*modelRoot A K false 0 (a:K)=
      modelRoot A K false 0 (-(a⁻¹:Kˣ):K)*torusNode K 0 (-a⁻¹)*
        modelRoot A K true 0 (a⁻¹:Kˣ) := by
  have hw : weylParameter K 0 1=shortWord K := by
    simp [weylParameter,shortWord]
  simpa only [hw,Units.val_one,one_pow,neg_mul,one_mul,neg_one_mul]
    using shortParameter_gauss K 1 a

theorem longWord_gauss (a : Kˣ) :
    longWord K*modelRoot A K false 1 (a:K)=
      modelRoot A K false 1 (-(a⁻¹:Kˣ):K)*torusNode K 1 a⁻¹*
        modelRoot A K true 1 (a⁻¹:Kˣ) := by
  have hw : weylParameter K 1 (-1)=longWord K := by
    simp [weylParameter,longWord]
  simpa only [hw,Units.val_neg,Units.val_one,neg_one_sq,one_mul,neg_mul,
    neg_neg,one_mul] using longParameter_gauss K (-1) a

theorem simple_gauss (i : Fin 2) (a : K) (ha : a≠0) :
    ∃ c∈borel K,∃ d : K,
      simpleWeyl K i*positiveModel K (simpleIndex i) a=
        c*modelRoot A K true i d := by
  let u : Kˣ := Units.mk0 a ha
  have hu : (u:K)=a := rfl
  fin_cases i
  · refine ⟨modelRoot A K false 0 (-(u⁻¹:Kˣ):K)*torusNode K 0 (-u⁻¹),?_,
      (u⁻¹:Kˣ),?_⟩
    · apply (borel K).mul_mem
      · apply positive_le_borel K
        exact (positiveElement K 0 (-(u⁻¹:Kˣ):K)).property
      · exact torus_le_borel K (torusNode_mem K 0 (-u⁻¹))
    · change shortWord K*modelRoot A K false 0 a=_
      simpa only [hu] using shortWord_gauss K u
  · refine ⟨modelRoot A K false 1 (-(u⁻¹:Kˣ):K)*torusNode K 1 u⁻¹,?_,
      (u⁻¹:Kˣ),?_⟩
    · apply (borel K).mul_mem
      · apply positive_le_borel K
        exact (positiveElement K 1 (-(u⁻¹:Kˣ):K)).property
      · exact torus_le_borel K (torusNode_mem K 1 u⁻¹)
    · change longWord K*modelRoot A K false 1 a=_
      simpa only [hu] using longWord_gauss K u

end SymmetricSubgroupAsymptotics.CFSGGTwoOriginalSimpleGauss
