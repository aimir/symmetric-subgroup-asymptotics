import SymmetricSubgroupAsymptotics.CFSGTrialityGeckFixedPositiveGeneration
import SymmetricSubgroupAsymptotics.CFSGTrialityGeckRelativeOpposition
import SymmetricSubgroupAsymptotics.CFSGTrialityGeckOvergroupWeylExtraction

/-! All genuinely fixed signed simple parameters generate the entire
actual folded D4 root-generated group, over arbitrary finite fields and
arbitrary field automorphisms. The scalar fixedness conditions are proved
for section parameters by actual fixed-height peeling; no presentation
or fixed-point quotient-surjectivity premise is assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGTrialityGeckSimpleParameterGeneration
open CFSGTrialityD4NormTwo CFSGTrialityGeckDiagramCovariance
open CFSGTrialityGeckFixedPositiveGeneration CFSGTrialityGeckSectionQuotientCoordinates
open CFSGTrialityGeckFixedRootSections CFSGTrialityGeckFixedRootWords
open CFSGTrialityGeckRelativeRootGenerated CFSGTrialityGeckRelativeOpposition
open CFSGTrialityGeckOvergroupWeylExtraction CFSGTrialityGeckSimpleOrbitFlags
open CFSGTrialityGeckPositiveTwist CFSGTrialityRelativeWordLanguage
open CFSGNormTwoGeckWeylWordAlgebra CFSGNormTwoGeckWeylWordDegree CFSGNormTwoGeckIntegralWord
open CFSGSerreQuadraticMatrix CFSGSerreQuadraticWeylWord

theorem fixedRootGenerated_le_of_simple_parameters (K : Type) [Field K] [Finite K]
    (sigma : K≃+*K) (H : Subgroup (Matrix GeckIndex GeckIndex K)ˣ)
    (hshort : ∀neg t,sigma (sigma (sigma t))=t→shortOrbit K sigma neg t∈H)
    (hmiddle : ∀neg t,sigma t=t→canonicalRoot rawData K neg 1 t∈H) :
    fixedRootGenerated K sigma≤H := by
  have hshortW : shortWeyl K∈H := by
    have he := orbit_word_parameter K sigma false
    change shortWeyl K=shortOrbit K sigma false 1*shortOrbit K sigma true (-1)*
      shortOrbit K sigma false 1 at he
    rw [he]
    exact H.mul_mem (H.mul_mem (hshort false 1 (by simp)) (hshort true (-1) (by simp)))
      (hshort false 1 (by simp))
  have hlongW : longWeyl K∈H := by
    have he := orbit_word_parameter K sigma true
    change longWeyl K=canonicalRoot rawData K false 1 1*canonicalRoot rawData K true 1 (-1)*
      canonicalRoot rawData K false 1 1 at he
    rw [he]
    exact H.mul_mem (H.mul_mem (hmiddle false 1 (by simp)) (hmiddle true (-1) (by simp)))
      (hmiddle false 1 (by simp))
  have hshortT (s : Fin 3) : shortTransport K s∈H := by
    fin_cases s
    · exact H.one_mem
    · exact hlongW
    · exact H.mul_mem hshortW hlongW
  have hlongT (s : Fin 3) : longTransport K s∈H := by
    fin_cases s
    · exact H.one_mem
    · exact hshortW
    · exact H.mul_mem hlongW hshortW
  have hshortS (s : Fin 3) (t : K) (ht : sigma (sigma (sigma t))=t) :
      shortSection K sigma s false t∈H :=
    H.mul_mem (H.mul_mem (hshortT s) (hshort false t ht)) (H.inv_mem (hshortT s))
  have hlongS (s : Fin 3) (t : K) (ht : sigma t=t) : longSection K s false t∈H :=
    H.mul_mem (H.mul_mem (hlongT s) (hmiddle false t ht)) (H.inv_mem (hlongT s))
  have hsections : sectionGenerated K sigma≤H.comap (PositiveGroup K).subtype := by
    apply (Subgroup.closure_le _).mpr
    rintro _ (⟨s,t,ht,rfl⟩|⟨s,t,ht,rfl⟩)
    · change (longPositiveSection K s t).val∈H
      rw [longPositiveSection_val]
      exact hlongS s t.toAdd ht
    · change (shortPositiveSection K sigma s t).val∈H
      rw [shortPositiveSection_val]
      exact hshortS s t.toAdd ht
  have hpositive : signedFixed K sigma false≤H := by
    intro u hu
    let v : PositiveGroup K := ⟨u,hu.1⟩
    have hvfix : positiveTwist K sigma v=v := by
      apply Subtype.ext
      exact (positiveTwist_val K sigma v).trans hu.2
    have hv : v∈fixedPositive K sigma := hvfix
    rw [fixedPositive_eq_sectionGenerated] at hv
    exact hsections hv
  have hword (r : List Bool) : wordUnit (CartanMatrix.D 4) (CartanMatrix.D_transpose 4)
      D4_positive_definite Base Index K (expandRelative r)∈H := by
    induction r with
    | nil=>exact H.one_mem
    | cons a r ih=>
      cases a
      · rw [expandRelative,wordUnit_append]
        apply H.mul_mem _ ih
        simpa only [word_eq_canonicalWord,shortWeyl] using hshortW
      · rw [expandRelative,wordUnit_append]
        apply H.mul_mem _ ih
        simpa only [word_eq_canonicalWord,longWeyl] using hlongW
  have hO : relativeOpposition K∈H := hword oppositionRelativeWord
  have hnegative : signedFixed K sigma true≤H := by
    rw [←fixed_positive_image_eq_fixed_negative]
    rintro _ ⟨u,hu,rfl⟩
    exact H.mul_mem (H.mul_mem hO (hpositive hu)) (H.inv_mem hO)
  exact sup_le hpositive hnegative

end SymmetricSubgroupAsymptotics.CFSGTrialityGeckSimpleParameterGeneration
