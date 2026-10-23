import SymmetricSubgroupAsymptotics.CFSGTrialityGeckNormalizedNegativeOne

/-! After the positive scalar constants are normalized, the actual
rank-one constraint fixes the simple Weyl words. Their literal
conjugation identities propagate both field maps to the opposite signs.
No arbitrary-parameter Weyl formula or common-field restriction is
assumed here. -/
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTrialityGeckOriginalSignedSemilinear
open CFSGTrialityD4NormTwo CFSGTrialityGeckDiagramCovariance
open CFSGTrialityGeckOriginalSimpleParameters CFSGTrialityGeckSignedSimpleParameters
open CFSGTrialityGeckNormalizedNegativeOne CFSGTrialityGeckGeneratedOriginalProjection
open CFSGTrialityGeckRelativeRootGenerated CFSGTrialityGeckFixedRootWords
open CFSGTrialityGeckSimpleChartWeyl CFSGTrialityGeckSimpleOrbitFlags
open CFSGTrialityGeckOvergroupWeylExtraction CFSGTrialityGeckOriginalRootFamily
open CFSGTrialityGeckOriginalOppositeAlignment CFSGTrialityFixedField
open CFSGSerreQuadraticWeylWord CFSGSerreOrdinaryTwists CFSGSerreQuadraticMatrix
local instance : DecidableEq (CFSGNormTwoRootPairing.Roots (CartanMatrix.D 4)) := Classical.decEq _

def shortWeylElement (q : CFSG.PrimePower) [IsSimpleGroup (CFSG.Models.TrialityD4 q)] :
    CFSG.Models.TrialityD4 q :=
  originalShortHom q false (Multiplicative.ofAdd 1)*originalShortHom q true (Multiplicative.ofAdd (-1))*
    originalShortHom q false (Multiplicative.ofAdd 1)

def middleWeylElement (q : CFSG.PrimePower) [IsSimpleGroup (CFSG.Models.TrialityD4 q)] :
    CFSG.Models.TrialityD4 q :=
  originalMiddleHom q false (Multiplicative.ofAdd 1)*originalMiddleHom q true (Multiplicative.ofAdd (-1))*
    originalMiddleHom q false (Multiplicative.ofAdd 1)

theorem short_weyl_root_conjugation (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.TrialityD4 q)] (t : q.Extension 3) :
    shortWeylElement q*originalShortHom q false (Multiplicative.ofAdd t)*(shortWeylElement q)⁻¹=
      originalShortHom q true (Multiplicative.ofAdd (-t)) := by
  have hraw :
      (shortGeneratedHom q false (Multiplicative.ofAdd 1)*shortGeneratedHom q true (Multiplicative.ofAdd (-1))*
        shortGeneratedHom q false (Multiplicative.ofAdd 1))*shortGeneratedHom q false (Multiplicative.ofAdd t)*
      (shortGeneratedHom q false (Multiplicative.ofAdd 1)*shortGeneratedHom q true (Multiplicative.ofAdd (-1))*
        shortGeneratedHom q false (Multiplicative.ofAdd 1))⁻¹=
      shortGeneratedHom q true (Multiplicative.ofAdd (-t)) := by
    apply Subtype.ext
    have hw := orbit_word_parameter (q.Extension 3) (definingFieldAutomorphism q 3) false
    change canonicalWord rawData (q.Extension 3) (orbitWord false)=
      shortOrbit (q.Extension 3) (definingFieldAutomorphism q 3) false 1*
        shortOrbit (q.Extension 3) (definingFieldAutomorphism q 3) true (-1)*
        shortOrbit (q.Extension 3) (definingFieldAutomorphism q 3) false 1 at hw
    change (shortOrbit (q.Extension 3) (definingFieldAutomorphism q 3) false 1*
      shortOrbit (q.Extension 3) (definingFieldAutomorphism q 3) true (-1)*
      shortOrbit (q.Extension 3) (definingFieldAutomorphism q 3) false 1)*shortOrbit (q.Extension 3) (definingFieldAutomorphism q 3) false t*
      (shortOrbit (q.Extension 3) (definingFieldAutomorphism q 3) false 1*
      shortOrbit (q.Extension 3) (definingFieldAutomorphism q 3) true (-1)*
      shortOrbit (q.Extension 3) (definingFieldAutomorphism q 3) false 1)⁻¹=shortOrbit (q.Extension 3) (definingFieldAutomorphism q 3) true (-t)
    rw [←hw]
    exact short_word_conjugates _ _ t
  simpa only [map_mul,map_inv,shortWeylElement,originalShortHom,MonoidHom.comp_apply] using
    congrArg (generatedToOriginal q) hraw

theorem middle_weyl_root_conjugation (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.TrialityD4 q)] (t : fixedField q) :
    middleWeylElement q*originalMiddleHom q false (Multiplicative.ofAdd t)*(middleWeylElement q)⁻¹=
      originalMiddleHom q true (Multiplicative.ofAdd (-t)) := by
  have hraw :
      (middleGeneratedHom q false (Multiplicative.ofAdd 1)*middleGeneratedHom q true (Multiplicative.ofAdd (-1))*
        middleGeneratedHom q false (Multiplicative.ofAdd 1))*middleGeneratedHom q false (Multiplicative.ofAdd t)*
      (middleGeneratedHom q false (Multiplicative.ofAdd 1)*middleGeneratedHom q true (Multiplicative.ofAdd (-1))*
        middleGeneratedHom q false (Multiplicative.ofAdd 1))⁻¹=
      middleGeneratedHom q true (Multiplicative.ofAdd (-t)) := by
    apply Subtype.ext
    have hw := orbit_word_parameter (q.Extension 3) (definingFieldAutomorphism q 3) true
    change canonicalWord rawData (q.Extension 3) (orbitWord true)=
      canonicalRoot rawData (q.Extension 3) false 1 1*canonicalRoot rawData (q.Extension 3) true 1 (-1)*
        canonicalRoot rawData (q.Extension 3) false 1 1 at hw
    change (canonicalRoot rawData (q.Extension 3) false 1 1*canonicalRoot rawData (q.Extension 3) true 1 (-1)*
      canonicalRoot rawData (q.Extension 3) false 1 1)*canonicalRoot rawData (q.Extension 3) false 1 t.val*
      (canonicalRoot rawData (q.Extension 3) false 1 1*canonicalRoot rawData (q.Extension 3) true 1 (-1)*
      canonicalRoot rawData (q.Extension 3) false 1 1)⁻¹=canonicalRoot rawData (q.Extension 3) true 1 (-t.val)
    rw [←hw]
    exact middle_word_conjugates _ t.val
  simpa only [map_mul,map_inv,middleWeylElement,originalMiddleHom,MonoidHom.comp_apply] using
    congrArg (generatedToOriginal q) hraw

private theorem opposite_action {K G:Type*} [Field K] [Group G]
    (X Y:Multiplicative K→*G) (w:G)
    (hw:∀t:K,w*X (Multiplicative.ofAdd t)*w⁻¹=Y (Multiplicative.ofAdd (-t)))
    (f:MulAut G) (hfw:f w=w) (sigma:K≃+*K)
    (hX:∀t:K,f (X (Multiplicative.ofAdd t))=X (Multiplicative.ofAdd (sigma t))) :
    ∀t:K,f (Y (Multiplicative.ofAdd t))=Y (Multiplicative.ofAdd (sigma t)) := by
  intro t
  have he := congrArg f (hw (-t))
  simp only [neg_neg,map_mul,map_inv,hfw,hX,map_neg] at he
  rw [hw] at he
  simpa only [neg_neg] using he.symm

theorem signed_short_parameter_action (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.TrialityD4 q)] (f : MulAut (CFSG.Models.TrialityD4 q))
    (hp : (originalSylow q).map f.toMonoidHom=originalSylow q)
    (hn : (originalNegative q).map f.toMonoidHom=originalNegative q)
    (sigma : q.Extension 3≃+*q.Extension 3)
    (hX : ∀t,f (originalShortHom q false (Multiplicative.ofAdd t))=
      originalShortHom q false (Multiplicative.ofAdd (sigma t))) :
    ∀(neg:Bool) t,f (originalShortHom q neg (Multiplicative.ofAdd t))=
      originalShortHom q neg (Multiplicative.ofAdd (sigma t)) := by
  have h1 : f (originalShortHom q false (Multiplicative.ofAdd 1))=
      originalShortHom q false (Multiplicative.ofAdd 1) := by simpa only [map_one] using hX 1
  have hy1 := short_negative_one_fixed q f hp hn h1
  have hw : f (shortWeylElement q)=shortWeylElement q := by
    simp only [shortWeylElement,map_mul,h1,hy1]
  intro neg
  cases neg
  · exact hX
  · exact opposite_action (originalShortHom q false) (originalShortHom q true)
      (shortWeylElement q) (short_weyl_root_conjugation q) f hw sigma hX

theorem signed_middle_parameter_action (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.TrialityD4 q)] (f : MulAut (CFSG.Models.TrialityD4 q))
    (hp : (originalSylow q).map f.toMonoidHom=originalSylow q)
    (hn : (originalNegative q).map f.toMonoidHom=originalNegative q)
    (tau : fixedField q≃+*fixedField q)
    (hX : ∀t:fixedField q,f (originalMiddleHom q false (Multiplicative.ofAdd t))=
      originalMiddleHom q false (Multiplicative.ofAdd (tau t))) :
    ∀(neg:Bool) (t:fixedField q),f (originalMiddleHom q neg (Multiplicative.ofAdd t))=
      originalMiddleHom q neg (Multiplicative.ofAdd (tau t)) := by
  have h1 : f (originalMiddleHom q false (Multiplicative.ofAdd 1))=
      originalMiddleHom q false (Multiplicative.ofAdd 1) := by simpa only [map_one] using hX 1
  have hy1 := middle_negative_one_fixed q f hp hn h1
  have hw : f (middleWeylElement q)=middleWeylElement q := by
    simp only [middleWeylElement,map_mul,h1,hy1]
  intro neg
  cases neg
  · exact hX
  · exact opposite_action (originalMiddleHom q false) (originalMiddleHom q true)
      (middleWeylElement q) (middle_weyl_root_conjugation q) f hw tau hX

end SymmetricSubgroupAsymptotics.CFSGTrialityGeckOriginalSignedSemilinear
