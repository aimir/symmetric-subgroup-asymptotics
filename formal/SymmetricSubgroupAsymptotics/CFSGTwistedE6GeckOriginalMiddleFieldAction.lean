import SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckOriginalMiddleTorus

/-! Actual images of the two middle factors under an ORIGINAL Aut.
Signed A2 parameter data determines its Weyl images; literal torus
scaling then gives both higher-root parameter actions. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckOriginalMiddleFieldAction
open CFSGTwistedE6GeckOriginalMiddleTorus CFSGTwistedE6GeckOriginalMiddleCollecting
open CFSGTwistedE6GeckRelativeTorus CFSGTwistedE6GeckOriginalSimpleParameters
open CFSGTwistedE6GeckOriginalPairedA2 CFSGTwistedE6GeckOriginalSingletonA2
open CFSGTwistedE6GeckOriginalProjection

private theorem image_conjugate {G : Type*} [Group G] (f : G→*G) (W H x y : G)
    (hW : f W=H*W) (hx : f x=y) :
    f (W*x*W⁻¹)=H*(W*y*W⁻¹)*H⁻¹ := by
  rw [map_mul,map_mul,map_inv,hW,hx]
  group

theorem middleShort_image (q : CFSG.PrimePower) [IsSimpleGroup (CFSG.Models.TwistedE6 q)]
    (f : MulAut (CFSG.Models.TwistedE6 q)) (tau : RingAut (q.Extension 2)) (kap : RingAut (Coefficient q))
    (d : (q.Extension 2)ˣ) (e : (Coefficient q)ˣ)
    (hpair : ∀a,f (pairedOriginalHom q false 1 (Multiplicative.ofAdd a))=
      pairedOriginalHom q false 1 (Multiplicative.ofAdd ((d : q.Extension 2)*tau a)))
    (hsingle : ∀a,f (singletonOriginalHom q false 1 (Multiplicative.ofAdd a))=
      singletonOriginalHom q false 1 (Multiplicative.ofAdd ((e : Coefficient q)*kap a)))
    (hnegative : ∀a,f (singletonOriginalHom q true 1 (Multiplicative.ofAdd a))=
      singletonOriginalHom q true 1 (Multiplicative.ofAdd ((e : Coefficient q)⁻¹*kap a))) (a : q.Extension 2) :
    f (middleShortOriginalHom q (Multiplicative.ofAdd a))=
      middleShortOriginalHom q (Multiplicative.ofAdd
        ((((e : Coefficient q) : q.Extension 2)*(d : q.Extension 2))*tau a)) := by
  have hW := singleton_weyl_image q f 1 kap e hsingle hnegative
  change f (generatedToOriginal q (simpleWeylGenerated q 2))=
    generatedToOriginal q (singletonTorusGenerated q 1 e)*generatedToOriginal q (simpleWeylGenerated q 2) at hW
  have he := image_conjugate f.toMonoidHom
    (generatedToOriginal q (simpleWeylGenerated q 2)) (generatedToOriginal q (singletonTorusGenerated q 1 e))
    (pairedOriginalHom q false 1 (Multiplicative.ofAdd a))
    (pairedOriginalHom q false 1 (Multiplicative.ofAdd ((d : q.Extension 2)*tau a))) hW (hpair a)
  change f (middleShortOriginalHom q (Multiplicative.ofAdd a))=
    generatedToOriginal q (singletonTorusGenerated q 1 e)*
      middleShortOriginalHom q (Multiplicative.ofAdd ((d : q.Extension 2)*tau a))*
      (generatedToOriginal q (singletonTorusGenerated q 1 e))⁻¹ at he
  rw [original_singleton_torus_middleShort] at he
  refine he.trans ?_
  apply congrArg (fun x : q.Extension 2=>middleShortOriginalHom q (Multiplicative.ofAdd x))
  ring

theorem middleLong_image (q : CFSG.PrimePower) [IsSimpleGroup (CFSG.Models.TwistedE6 q)]
    (f : MulAut (CFSG.Models.TwistedE6 q)) (tau : RingAut (q.Extension 2)) (kap : RingAut (Coefficient q))
    (d : (q.Extension 2)ˣ) (e : (Coefficient q)ˣ)
    (hpair : ∀a,f (pairedOriginalHom q false 1 (Multiplicative.ofAdd a))=
      pairedOriginalHom q false 1 (Multiplicative.ofAdd ((d : q.Extension 2)*tau a)))
    (hnegative : ∀a,f (pairedOriginalHom q true 1 (Multiplicative.ofAdd a))=
      pairedOriginalHom q true 1 (Multiplicative.ofAdd ((d : q.Extension 2)⁻¹*tau a)))
    (hsingle : ∀a,f (singletonOriginalHom q false 1 (Multiplicative.ofAdd a))=
      singletonOriginalHom q false 1 (Multiplicative.ofAdd ((e : Coefficient q)*kap a))) (a : Coefficient q) :
    f (middleLongOriginalHom q (Multiplicative.ofAdd a))=
      middleLongOriginalHom q (Multiplicative.ofAdd
        ((normCoefficient q (d : q.Extension 2)*(e : Coefficient q))*kap a)) := by
  have hW := paired_weyl_image q f 1 tau d hpair hnegative
  change f (generatedToOriginal q (simpleWeylGenerated q 1))=
    generatedToOriginal q (pairedTorusGenerated q 1 d)*generatedToOriginal q (simpleWeylGenerated q 1) at hW
  have he := image_conjugate f.toMonoidHom
    (generatedToOriginal q (simpleWeylGenerated q 1)) (generatedToOriginal q (pairedTorusGenerated q 1 d))
    (singletonOriginalHom q false 1 (Multiplicative.ofAdd a))
    (singletonOriginalHom q false 1 (Multiplicative.ofAdd ((e : Coefficient q)*kap a))) hW (hsingle a)
  change f (middleLongOriginalHom q (Multiplicative.ofAdd a))=
    generatedToOriginal q (pairedTorusGenerated q 1 d)*
      middleLongOriginalHom q (Multiplicative.ofAdd ((e : Coefficient q)*kap a))*
      (generatedToOriginal q (pairedTorusGenerated q 1 d))⁻¹ at he
  rw [original_paired_torus_middleLong] at he
  refine he.trans ?_
  apply congrArg (fun x : Coefficient q=>middleLongOriginalHom q (Multiplicative.ofAdd x))
  ring

end SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckOriginalMiddleFieldAction
