import SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckOriginalProductTorusAction
import SymmetricSubgroupAsymptotics.CFSGRankOneTorusFieldCoupling

/-! The literal long-axis rank-one torus acts with exponent minus one
on the short chart. This word identifies the two axis field actions
without a power-surjectivity assumption or a lift of an automorphism. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckOriginalMiddleTorus
open CFSGGTwoD4GeckOriginalProductTorusAction CFSGGTwoD4GeckOriginalSimpleParameters
open CFSGGTwoD4GeckOriginalProjection CFSGGTwoD4GeckRelativeProductTorus
open CFSGGTwoD4GeckProductTorusParameters CFSGGTwoD4GeckScalarTorus
open CFSGTrialityGeckRelativeRootGenerated CFSGGTwoD4GeckSimpleParameters
open CFSGRankOneTorusFieldCoupling CFSG.Models.Chevalley
variable (K : Type) [Field K] [Finite K] [IsSimpleGroup (Projective CartanMatrix.G₂ K)]

def originalMiddleTorus (c : Kˣ) : Projective CartanMatrix.G₂ K :=
  originalProductTorus K ![1,c]

private theorem relativeProductTorus_middle_node (c : Kˣ) :
    relativeProductTorus K ![1,c]=relativeTorusNode K true c := by
  have he : relativeProductTorus K ![1,c]=relativeTorusWord K ![1,c] := by
    apply Subtype.ext
    exact (relativeTorusWord_val K ![1,c]).symm
  rw [he]
  change (relativeWeylWord K false 1*(relativeWeylWord K false 1)⁻¹)*
    relativeTorusNode K true c=relativeTorusNode K true c
  group

theorem originalMiddleTorus_eq_node (c : Kˣ) :
    originalMiddleTorus K c=generatedToOriginal K (relativeTorusNode K true c) := by
  change generatedToOriginal K (relativeProductTorus K ![1,c])=_
  rw [relativeProductTorus_middle_node]

theorem originalMiddleTorus_eq_torusWord (c : Kˣ) :
    originalMiddleTorus K c=torusWord (fun neg=>originalSimpleHom K neg true) c := by
  rw [originalMiddleTorus_eq_node]
  simp only [relativeTorusNode,relativeWeylWord,map_mul,map_inv,
    torusWord,weylWord,originalSimpleHom_apply]

theorem originalMiddleTorus_word (c : Kˣ) :
    originalMiddleTorus K c=
      originalSimpleHom K false true (Multiplicative.ofAdd (c:K))*
      originalSimpleHom K true true (Multiplicative.ofAdd (-(c:K)⁻¹))*
      originalSimpleHom K false true (Multiplicative.ofAdd (c:K))*
      originalSimpleHom K false true (Multiplicative.ofAdd (-1:K))*
      originalSimpleHom K true true (Multiplicative.ofAdd (1:K))*
      originalSimpleHom K false true (Multiplicative.ofAdd (-1:K)) := by
  rw [originalMiddleTorus_eq_torusWord]
  have hi (neg : Bool) (t : K) :
      (originalSimpleHom K neg true (Multiplicative.ofAdd t))⁻¹=
        originalSimpleHom K neg true (Multiplicative.ofAdd (-t)) :=
    (map_inv (originalSimpleHom K neg true) (Multiplicative.ofAdd t)).symm
  simp only [torusWord,weylWord,Units.val_one,inv_one,mul_inv_rev,hi,neg_neg]
  group

private theorem middle_scalar (c : Kˣ) :
    parameterScalar K ![1,c] false false=c⁻¹ := by
  change scalarEquiv Kˣ ![1,c] 0=c⁻¹
  rw [scalarEquiv_short]
  change (1:Kˣ)^2/c=c⁻¹
  simp only [one_pow,one_div]

theorem originalMiddleTorus_short_action (c : Kˣ) (t : K) :
    originalMiddleTorus K c*originalSimpleHom K false false (Multiplicative.ofAdd t)*
      (originalMiddleTorus K c)⁻¹=
        originalSimpleHom K false false (Multiplicative.ofAdd ((c:K)⁻¹*t)) := by
  have he := originalProductTorus_simple_action K ![1,c] false false t
  rw [middle_scalar,Units.val_inv_eq_inv_val,mul_comm t] at he
  exact he

theorem long_torusWord_short_action (c : Kˣ) (t : K) :
    torusWord (fun neg=>originalSimpleHom K neg true) c*
        originalSimpleHom K false false (Multiplicative.ofAdd t)*
        (torusWord (fun neg=>originalSimpleHom K neg true) c)⁻¹=
      originalSimpleHom K false false (Multiplicative.ofAdd ((c:K)⁻¹*t)) := by
  rw [←originalMiddleTorus_eq_torusWord]
  exact originalMiddleTorus_short_action K c t

end SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckOriginalMiddleTorus
