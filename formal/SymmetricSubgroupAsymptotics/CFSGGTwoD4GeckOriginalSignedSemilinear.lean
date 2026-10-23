import SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckNormalizedNegativeOne

/-! A unital positive field action determines the opposite sign through
literal rank-one Weyl words. Every central-quotient rigidity premise is
discharged by the actual generated and original groups. -/
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckOriginalSignedSemilinear
open CFSGGTwoD4GeckNormalizedNegativeOne CFSGGTwoD4GeckOriginalSimpleParameters
open CFSGGTwoD4GeckOriginalProjection CFSGGTwoD4GeckSimpleParameters
open CFSG.Models.Chevalley
variable (K : Type) [Field K] [Finite K] [IsSimpleGroup (Projective CartanMatrix.G₂ K)]

def originalWeylElement (a : Bool) : Projective CartanMatrix.G₂ K :=
  originalSimpleHom K false a (Multiplicative.ofAdd 1)*
    originalSimpleHom K true a (Multiplicative.ofAdd (-1))*
      originalSimpleHom K false a (Multiplicative.ofAdd 1)

theorem original_weyl_root_conjugation (a : Bool) (t : K) :
    originalWeylElement K a*originalSimpleHom K false a (Multiplicative.ofAdd t)*
      (originalWeylElement K a)⁻¹ = originalSimpleHom K true a (Multiplicative.ofAdd (-t)) := by
  simpa only [map_mul,map_inv,originalSimpleHom,MonoidHom.comp_apply,originalWeylElement,
    generatedWeylElement] using congrArg (generatedToOriginal K) (generated_weyl_root_conjugation K a t)

private theorem opposite_action {L G : Type*} [Field L] [Group G]
    (X Y : Multiplicative L →* G) (w : G)
    (hw : ∀t:L,w*X (Multiplicative.ofAdd t)*w⁻¹=Y (Multiplicative.ofAdd (-t)))
    (f : MulAut G) (hfw : f w=w) (tau : RingAut L)
    (hX : ∀t:L,f (X (Multiplicative.ofAdd t))=X (Multiplicative.ofAdd (tau t))) :
    ∀t:L,f (Y (Multiplicative.ofAdd t))=Y (Multiplicative.ofAdd (tau t)) := by
  intro t
  have he := congrArg f (hw (-t))
  simp only [neg_neg,map_mul,map_inv,hfw,hX,map_neg] at he
  rw [hw] at he
  simpa only [neg_neg] using he.symm

theorem signed_parameter_action (p : ℕ) [Fact p.Prime] [CharP K p]
    (f : MulAut (Projective CartanMatrix.G₂ K)) (a : Bool) (tau : RingAut K)
    (hrange : (originalSimpleHom K true a).range.map f.toMonoidHom = (originalSimpleHom K true a).range)
    (hX : ∀t:K,f (originalSimpleHom K false a (Multiplicative.ofAdd t))=
      originalSimpleHom K false a (Multiplicative.ofAdd (tau t))) :
    ∀(neg:Bool) (t:K),f (originalSimpleHom K neg a (Multiplicative.ofAdd t))=
      originalSimpleHom K neg a (Multiplicative.ofAdd (tau t)) := by
  have h1 : f (originalSimpleHom K false a (Multiplicative.ofAdd 1))=
      originalSimpleHom K false a (Multiplicative.ofAdd 1) := by simpa only [map_one] using hX 1
  have hy1 := CFSGGTwoD4GeckNormalizedNegativeOne.negative_one_fixed K p f a hrange h1
  have hw : f (originalWeylElement K a)=originalWeylElement K a := by
    simp only [originalWeylElement,map_mul,h1,hy1]
  intro neg
  cases neg
  · exact hX
  · exact opposite_action (originalSimpleHom K false a) (originalSimpleHom K true a)
      (originalWeylElement K a) (original_weyl_root_conjugation K a) f hw tau hX

end SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckOriginalSignedSemilinear
