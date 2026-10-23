import SymmetricSubgroupAsymptotics.CFSGE6GeckSimpleGeneration
import SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckRelativeTorus

/-! Actual ORIGINAL automorphisms are determined by the displayed signed
simple parameters. The equalizer is pulled back along the literal J
projection, and genuine fixed-height generation proves it is all J.
Positive parameters alone suffice within the opposed-Sylow stabilizer,
by the already proved original mixed A2 negative-parameter rigidity. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckOriginalParameterFaithful
open CFSGE6GeckSimpleGeneration CFSGE6GeckFixedSimpleParameters
open CFSGTwistedE6GeckOriginalSimpleParameters CFSGTwistedE6GeckOriginalSingletonA2
open CFSGTwistedE6GeckRelativeTorus CFSGTwistedE6GeckOriginalProjection
open CFSGTwistedE6GeckOriginalOppositeAlignment CFSGTwistedE6GeckRelativeRootGenerated
open CFSGTwistedE6GeckDiagramCovariance CFSGTwistedE6GeckOriginalPairedSignedField
open CFSGTwistedE6GeckMatrixTwist
open CFSGTwistedE6GeckOriginalSingletonSignedField CFSGSerreOrdinaryTwists

theorem eq_one_of_signed_simple_parameters_fixed (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.TwistedE6 q)] (f : MulAut (CFSG.Models.TwistedE6 q))
    (hpair : ∀neg j a,f (pairedOriginalHom q neg j (Multiplicative.ofAdd a))=
      pairedOriginalHom q neg j (Multiplicative.ofAdd a))
    (hsingle : ∀neg j a,f (singletonOriginalHom q neg j (Multiplicative.ofAdd a))=
      singletonOriginalHom q neg j (Multiplicative.ofAdd a)) : f=1 := by
  let J := fixedRootGenerated (q.Extension 2) (definingFieldAutomorphism q 2)
  let pi := generatedToOriginal q
  let T : Subgroup J := (f.toMonoidHom.comp pi).eqLocus pi
  let S := T.map J.subtype
  have hSfixed : ∀u∈S,unitTwist (q.Extension 2) (definingFieldAutomorphism q 2) u=u := by
    rintro u ⟨g,hg,rfl⟩
    exact fixedRootGenerated_le_fixed (q.Extension 2) (definingFieldAutomorphism q 2) g.property
  have hSsingle (neg : Bool) (j : Fin 2) (a : Coefficient q) :
      CFSGE6GeckSignedSimpleParameters.rawSingletonHom (q.Extension 2) neg j
        (Multiplicative.ofAdd (a : q.Extension 2))∈S := by
    refine ⟨singletonSignedInGenerated q neg j (Multiplicative.ofAdd a),?_,rfl⟩
    exact hsingle neg j a
  have hSpair (neg : Bool) (j : Fin 2) (a : q.Extension 2) :
      CFSGE6GeckSignedSimpleParameters.rawPairedHom (q.Extension 2) (definingFieldAutomorphism q 2) neg j
        (Multiplicative.ofAdd a)∈S := by
    refine ⟨pairedSignedInGenerated q neg j (Multiplicative.ofAdd a),?_,rfl⟩
    exact hpair neg j a
  have hwhole : J≤S := generated_le_of_simple_charts (q.Extension 2) (definingFieldAutomorphism q 2)
    S hSsingle hSpair (coefficient_involutive q) hSfixed
  have hfix (g : J) : f (pi g)=pi g := by
    obtain ⟨h,hh,hval⟩ := hwhole g.property
    have he : h=g := Subtype.ext hval
    subst h
    exact hh
  apply MulEquiv.ext
  intro y
  obtain ⟨g,rfl⟩ := generatedToOriginal_surjective q y
  exact hfix g

theorem eq_one_of_positive_simple_parameters_fixed (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.TwistedE6 q)] (f : MulAut (CFSG.Models.TwistedE6 q))
    (hU : (originalPositiveSylow q : Subgroup (CFSG.Models.TwistedE6 q)).map f.toMonoidHom=
      (originalPositiveSylow q : Subgroup (CFSG.Models.TwistedE6 q)))
    (hV : (originalNegative q).map f.toMonoidHom=originalNegative q)
    (hpair : ∀j a,f (pairedOriginalHom q false j (Multiplicative.ofAdd a))=
      pairedOriginalHom q false j (Multiplicative.ofAdd a))
    (hsingle : ∀j a,f (singletonOriginalHom q false j (Multiplicative.ofAdd a))=
      singletonOriginalHom q false j (Multiplicative.ofAdd a)) : f=1 := by
  apply eq_one_of_signed_simple_parameters_fixed q f
  · intro neg j a
    cases neg
    · exact hpair j a
    · have hj : j≠j.rev := by fin_cases j <;> decide
      simpa only [RingEquiv.refl_apply,one_mul,inv_one] using
        paired_negative_of_positive q f hU hV j j.rev hj (RingEquiv.refl (q.Extension 2)) 1 1 one_ne_zero one_ne_zero
          (fun t=>by simpa only [RingEquiv.refl_apply,one_mul] using hpair j t)
          (fun t=>by simpa only [RingEquiv.refl_apply,one_mul] using hpair j.rev t) a
  · intro neg j a
    cases neg
    · exact hsingle j a
    · have hj : j≠j.rev := by fin_cases j <;> decide
      simpa only [RingEquiv.refl_apply,one_mul,inv_one] using
        singleton_negative_of_positive q f hU hV j j.rev hj (RingEquiv.refl (Coefficient q)) 1 1 one_ne_zero one_ne_zero
          (fun t=>by simpa only [RingEquiv.refl_apply,one_mul] using hsingle j t)
          (fun t=>by simpa only [RingEquiv.refl_apply,one_mul] using hsingle j.rev t) a

end SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckOriginalParameterFaithful
