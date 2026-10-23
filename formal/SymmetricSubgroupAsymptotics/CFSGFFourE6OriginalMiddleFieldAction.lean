import SymmetricSubgroupAsymptotics.CFSGFFourE6OriginalMiddleTorus
import Mathlib.Tactic.Group
import Mathlib.Tactic.Ring

/-! Signed end-edge field data gives the actual higher-root actions on
both original middle factors, via proved Weyl images and actual tori. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGFFourE6OriginalMiddleFieldAction
open CFSGFFourE6OriginalMiddleTorus CFSGFFourE6OriginalMiddleFactors
open CFSGFFourE6RelativeTorus CFSGFFourE6GeneratedOriginalProjection
open CFSGFFourE6OriginalSimpleParameters CFSGFFourE6SimpleGeneratedParameters
open CFSG.Models.Chevalley

private theorem image_conjugate {G : Type*} [Group G] (f : G→*G) (W H x y : G)
    (hW : f W=H*W) (hx : f x=y) : f (W*x*W⁻¹)=H*(W*y*W⁻¹)*H⁻¹ := by
  rw [map_mul,map_mul,map_inv,hW,hx]
  group

theorem middleShort_image (K : Type) [Field K] [Finite K]
    [IsSimpleGroup (Projective CartanMatrix.F₄ K)] (f : MulAut (Projective CartanMatrix.F₄ K))
    (tau kap : RingAut K) (d e : Kˣ)
    (hpair : ∀a,f (originalSimpleHom K false 1 (Multiplicative.ofAdd a))=
      originalSimpleHom K false 1 (Multiplicative.ofAdd ((d : K)*tau a)))
    (hsingle : ∀a,f (originalSimpleHom K false 2 (Multiplicative.ofAdd a))=
      originalSimpleHom K false 2 (Multiplicative.ofAdd ((e : K)*kap a)))
    (hnegative : ∀a,f (originalSimpleHom K true 2 (Multiplicative.ofAdd a))=
      originalSimpleHom K true 2 (Multiplicative.ofAdd ((e : K)⁻¹*kap a))) (a : K) :
    f (middleShortOriginalHom K (Multiplicative.ofAdd a))=
      middleShortOriginalHom K (Multiplicative.ofAdd (((e : K)*(d : K))*tau a)) := by
  have hW := original_weyl_image K f 2 kap e hsingle hnegative
  have he := image_conjugate f.toMonoidHom
    (generatedToOriginal K (simpleWeylInGenerated K 2)) (generatedToOriginal K (torusInGenerated K 2 e))
    (originalSimpleHom K false 1 (Multiplicative.ofAdd a))
    (originalSimpleHom K false 1 (Multiplicative.ofAdd ((d : K)*tau a))) hW (hpair a)
  change f (middleShortOriginalHom K (Multiplicative.ofAdd a))=
    generatedToOriginal K (torusInGenerated K 2 e)*
      middleShortOriginalHom K (Multiplicative.ofAdd ((d : K)*tau a))*
      (generatedToOriginal K (torusInGenerated K 2 e))⁻¹ at he
  rw [original_torus_middleShort] at he
  refine he.trans ?_
  apply congrArg (fun x : K => middleShortOriginalHom K (Multiplicative.ofAdd x))
  ring

theorem middleLong_image (K : Type) [Field K] [Finite K]
    [IsSimpleGroup (Projective CartanMatrix.F₄ K)] (f : MulAut (Projective CartanMatrix.F₄ K))
    (tau kap : RingAut K) (d e : Kˣ)
    (hpair : ∀a,f (originalSimpleHom K false 1 (Multiplicative.ofAdd a))=
      originalSimpleHom K false 1 (Multiplicative.ofAdd ((d : K)*tau a)))
    (hnegative : ∀a,f (originalSimpleHom K true 1 (Multiplicative.ofAdd a))=
      originalSimpleHom K true 1 (Multiplicative.ofAdd ((d : K)⁻¹*tau a)))
    (hsingle : ∀a,f (originalSimpleHom K false 2 (Multiplicative.ofAdd a))=
      originalSimpleHom K false 2 (Multiplicative.ofAdd ((e : K)*kap a))) (a : K) :
    f (middleLongOriginalHom K (Multiplicative.ofAdd a))=
      middleLongOriginalHom K (Multiplicative.ofAdd ((((d : K)*(d : K))*(e : K))*kap a)) := by
  have hW := original_weyl_image K f 1 tau d hpair hnegative
  have he := image_conjugate f.toMonoidHom
    (generatedToOriginal K (simpleWeylInGenerated K 1)) (generatedToOriginal K (torusInGenerated K 1 d))
    (originalSimpleHom K false 2 (Multiplicative.ofAdd a))
    (originalSimpleHom K false 2 (Multiplicative.ofAdd ((e : K)*kap a))) hW (hsingle a)
  change f (middleLongOriginalHom K (Multiplicative.ofAdd a))=
    generatedToOriginal K (torusInGenerated K 1 d)*
      middleLongOriginalHom K (Multiplicative.ofAdd ((e : K)*kap a))*
      (generatedToOriginal K (torusInGenerated K 1 d))⁻¹ at he
  rw [original_torus_middleLong] at he
  refine he.trans ?_
  apply congrArg (fun x : K => middleLongOriginalHom K (Multiplicative.ofAdd x))
  ring

end SymmetricSubgroupAsymptotics.CFSGFFourE6OriginalMiddleFieldAction
