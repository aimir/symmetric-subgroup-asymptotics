import SymmetricSubgroupAsymptotics.CFSGFFourE6OriginalFieldAgreement
import SymmetricSubgroupAsymptotics.CFSGE6GeckSimpleGeneration

/-! Native signed F4 simple parameters generate the SAME actual J
source, so their original images determine every original automorphism.
Inside the signed label kernel, positive parameters alone are faithful. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGFFourE6OriginalParameterFaithful
open CFSGFFourE6OriginalFieldAgreement CFSGFFourE6OriginalSimpleParameters
open CFSGFFourE6SimpleGeneratedParameters CFSGFFourE6GeneratedOriginalProjection
open CFSGE6GeckSimpleGeneration CFSGE6GeckFixedSimpleParameters
open CFSGE6GeckFixedOrbitRootGroups CFSGE6GeckSignedSimpleParameters
open CFSGTwistedE6GeckRelativeRootGenerated CFSGTwistedE6GeckDiagramCovariance
open CFSGTwistedE6GeckMatrixTwist CFSGE6GeckRelativeSimpleHom CFSG.Models.Chevalley

theorem eq_one_of_signed_parameters_fixed (K : Type) [Field K] [Finite K]
    [IsSimpleGroup (Projective CartanMatrix.F₄ K)] (f : MulAut (Projective CartanMatrix.F₄ K))
    (hparam : ∀neg i a,f (originalSimpleHom K neg i (Multiplicative.ofAdd a))=
      originalSimpleHom K neg i (Multiplicative.ofAdd a)) : f=1 := by
  let J := fixedRootGenerated K (RingEquiv.refl K)
  let pi := generatedToOriginal K
  let T : Subgroup J := (f.toMonoidHom.comp pi).eqLocus pi
  let S := T.map J.subtype
  have hSfixed : ∀u∈S,unitTwist K (RingEquiv.refl K) u=u := by
    rintro u ⟨g,hg,rfl⟩
    exact fixedRootGenerated_le_fixed K (RingEquiv.refl K) g.property
  have hsingle (neg : Bool) (j : Fin 2) (a : fixedCoefficient K (RingEquiv.refl K)) :
      rawSingletonHom K neg j (Multiplicative.ofAdd (a : K))∈S := by
    refine ⟨simpleInGenerated K neg (singletonOrbit j) (Multiplicative.ofAdd (a : K)),?_,?_⟩
    · exact hparam neg (singletonOrbit j) a
    · change (simpleInGenerated K neg (singletonOrbit j) (Multiplicative.ofAdd (a : K))).val=_
      rw [simpleInGenerated_val]
      fin_cases j <;> rfl
  have hpair (neg : Bool) (j : Fin 2) (a : K) :
      rawPairedHom K (RingEquiv.refl K) neg j (Multiplicative.ofAdd a)∈S := by
    refine ⟨simpleInGenerated K neg (pairedOrbit j) (Multiplicative.ofAdd a),?_,?_⟩
    · exact hparam neg (pairedOrbit j) a
    · change (simpleInGenerated K neg (pairedOrbit j) (Multiplicative.ofAdd a)).val=_
      rw [simpleInGenerated_val]
      fin_cases j <;> rfl
  have hwhole : J≤S := generated_le_of_simple_charts K (RingEquiv.refl K) S hsingle hpair
    (fun _ => rfl) hSfixed
  have hfix (g : J) : f (pi g)=pi g := by
    obtain ⟨h,hh,hval⟩ := hwhole g.property
    have he : h=g := Subtype.ext hval
    subst h
    exact hh
  apply MulEquiv.ext
  intro y
  obtain ⟨g,rfl⟩ := generatedToOriginal_surjective K y
  exact hfix g

theorem eq_one_of_positive_parameters_fixed (K : Type) [Field K] [Finite K]
    (p : ℕ) [Fact p.Prime] [CharP K p] [IsSimpleGroup (Projective CartanMatrix.F₄ K)]
    (f : MulAut (Projective CartanMatrix.F₄ K))
    (hfix : ∀neg i,(originalSimpleHom K neg i).range.map f.toMonoidHom=(originalSimpleHom K neg i).range)
    (hpos : ∀i a,f (originalSimpleHom K false i (Multiplicative.ofAdd a))=
      originalSimpleHom K false i (Multiplicative.ofAdd a)) : f=1 := by
  obtain ⟨tau,c,hsem⟩ := exists_common_field_parameters K p f hfix
  have hc (i : Fin 4) (a : K) : (c i : K)*tau a=a := by
    have he := (hsem false i a).symm.trans (hpos i a)
    exact Multiplicative.ofAdd.injective (originalSimpleHom_injective K p false i he)
  have hcone (i : Fin 4) : (c i : K)=1 := by simpa only [map_one,mul_one] using hc i 1
  have htau (a : K) : tau a=a := by simpa only [hcone 0,one_mul] using hc 0 a
  apply eq_one_of_signed_parameters_fixed K f
  intro neg i a
  simpa only [hcone,htau,inv_one,ite_self,one_mul] using hsem neg i a

end SymmetricSubgroupAsymptotics.CFSGFFourE6OriginalParameterFaithful
