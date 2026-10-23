import SymmetricSubgroupAsymptotics.CFSGTrialityGeckOriginalSimpleParameters
import SymmetricSubgroupAsymptotics.CFSGTrialityGeckSimpleSignedGeneration

/-! The actual four signed charts determine homomorphisms on the SAME
original triality model. This uses proved literal generation of J and
its actual surjection onto the original group. A normalized signed
field description is therefore determined by its cubic-field map. -/
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTrialityGeckOriginalParameterFaithfulness
open CFSGTrialityD4NormTwo CFSGTrialityGeckDiagramCovariance
open CFSGTrialityGeckSignedSimpleParameters CFSGTrialityGeckOriginalSimpleParameters
open CFSGTrialityGeckSimpleSignedGeneration CFSGTrialityGeckGeneratedOriginalProjection
open CFSGTrialityGeckRelativeRootGenerated CFSGTrialityFixedField CFSGSerreOrdinaryTwists
local instance : DecidableEq (CFSGNormTwoRootPairing.Roots (CartanMatrix.D 4)) := Classical.decEq _

theorem original_hom_ext (q : CFSG.PrimePower) [IsSimpleGroup (CFSG.Models.TrialityD4 q)]
    {H : Type*} [Group H] (f g : CFSG.Models.TrialityD4 q→*H)
    (hX : ∀(neg:Bool) t,f (originalShortHom q neg (Multiplicative.ofAdd t))=
      g (originalShortHom q neg (Multiplicative.ofAdd t)))
    (hY : ∀(neg:Bool) (t:fixedField q),f (originalMiddleHom q neg (Multiplicative.ofAdd t))=
      g (originalMiddleHom q neg (Multiplicative.ofAdd t))) : f=g := by
  let J := fixedRootGenerated (q.Extension 3) (definingFieldAutomorphism q 3)
  let E : Subgroup J := (f.comp (generatedToOriginal q)).eqLocus (g.comp (generatedToOriginal q))
  have hJ : J≤E.map J.subtype := by
    apply fixedRootGenerated_le_of_simple_parameters q (E.map J.subtype)
    · intro neg t
      refine ⟨shortGeneratedHom q neg (Multiplicative.ofAdd t),?_,rfl⟩
      exact hX neg t
    · intro neg t
      refine ⟨middleGeneratedHom q neg (Multiplicative.ofAdd t),?_,rfl⟩
      exact hY neg t
  have heq : f.comp (generatedToOriginal q)=g.comp (generatedToOriginal q) := by
    ext z
    obtain ⟨y,hy,he⟩ := hJ z.property
    have hyz : y=z := Subtype.ext he
    exact hyz ▸ hy
  apply MonoidHom.ext
  intro x
  obtain ⟨z,hz⟩ := generatedToOriginal_surjective q x
  calc
    f x=f (generatedToOriginal q z) := congrArg f hz.symm
    _=g (generatedToOriginal q z) := congrArg (fun h:J→*H=>h z) heq
    _=g x := congrArg g hz

theorem original_aut_ext (q : CFSG.PrimePower) [IsSimpleGroup (CFSG.Models.TrialityD4 q)]
    (f g : MulAut (CFSG.Models.TrialityD4 q))
    (hX : ∀(neg:Bool) t,f (originalShortHom q neg (Multiplicative.ofAdd t))=
      g (originalShortHom q neg (Multiplicative.ofAdd t)))
    (hY : ∀(neg:Bool) (t:fixedField q),f (originalMiddleHom q neg (Multiplicative.ofAdd t))=
      g (originalMiddleHom q neg (Multiplicative.ofAdd t))) : f=g := by
  have hh := original_hom_ext q f.toMonoidHom g.toMonoidHom hX hY
  apply MulEquiv.ext
  intro x
  exact congrArg (fun h:CFSG.Models.TrialityD4 q→*CFSG.Models.TrialityD4 q=>h x) hh

theorem normalized_aut_eq_of_same_field (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.TrialityD4 q)] (f g : MulAut (CFSG.Models.TrialityD4 q))
    (sigma : q.Extension 3≃+*q.Extension 3) (tau eta : fixedField q≃+*fixedField q)
    (htau : ∀t:fixedField q,(tau t:q.Extension 3)=sigma (t:q.Extension 3))
    (heta : ∀t:fixedField q,(eta t:q.Extension 3)=sigma (t:q.Extension 3))
    (hfX : ∀(neg:Bool) t,f (originalShortHom q neg (Multiplicative.ofAdd t))=
      originalShortHom q neg (Multiplicative.ofAdd (sigma t)))
    (hgX : ∀(neg:Bool) t,g (originalShortHom q neg (Multiplicative.ofAdd t))=
      originalShortHom q neg (Multiplicative.ofAdd (sigma t)))
    (hfY : ∀(neg:Bool) (t:fixedField q),f (originalMiddleHom q neg (Multiplicative.ofAdd t))=
      originalMiddleHom q neg (Multiplicative.ofAdd (tau t)))
    (hgY : ∀(neg:Bool) (t:fixedField q),g (originalMiddleHom q neg (Multiplicative.ofAdd t))=
      originalMiddleHom q neg (Multiplicative.ofAdd (eta t))) : f=g := by
  apply original_aut_ext q f g
  · intro neg t
    exact (hfX neg t).trans (hgX neg t).symm
  · intro neg t
    have he : tau t=eta t := Subtype.ext ((htau t).trans (heta t).symm)
    exact (hfY neg t).trans ((congrArg (fun z=>originalMiddleHom q neg (Multiplicative.ofAdd z)) he).trans
      (hgY neg t).symm)

end SymmetricSubgroupAsymptotics.CFSGTrialityGeckOriginalParameterFaithfulness
