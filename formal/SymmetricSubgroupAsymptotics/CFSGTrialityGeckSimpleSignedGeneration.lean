import SymmetricSubgroupAsymptotics.CFSGTrialityGeckFixedPositiveGeneration
import SymmetricSubgroupAsymptotics.CFSGTrialityGeckRelativeOpposition
import SymmetricSubgroupAsymptotics.CFSGTrialityGeckOvergroupWeylExtraction
import SymmetricSubgroupAsymptotics.CFSGTrialityFixedField

/-! The four literal signed simple parameter charts generate the whole
actual relative-root group J. The proof uses proved fixed-section height
peeling and actual Weyl words. No folded BN presentation or fixed-point
quotient-surjectivity premise is supplied. -/
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGTrialityGeckSimpleSignedGeneration
open CFSGTrialityD4NormTwo CFSGTrialityGeckDiagramCovariance
open CFSGTrialityGeckFixedPositiveGeneration CFSGTrialityGeckSectionQuotientCoordinates
open CFSGTrialityGeckFixedRootSections CFSGTrialityGeckFixedRootWords
open CFSGTrialityGeckRelativeRootGenerated CFSGTrialityGeckRelativeOpposition
open CFSGTrialityGeckOvergroupWeylExtraction CFSGTrialityGeckSimpleOrbitFlags
open CFSGTrialityGeckPositiveTwist CFSGTrialityGeckMatrixTwist
open CFSGTrialityRelativeWordLanguage CFSGTrialityFixedField
open CFSGNormTwoGeckWeylWordAlgebra CFSGNormTwoGeckWeylWordDegree CFSGNormTwoGeckIntegralWord
open CFSGSerreQuadraticMatrix CFSGSerreQuadraticWeylWord CFSGSerreOrdinaryTwists
local instance : DecidableEq (CFSGNormTwoRootPairing.Roots (CartanMatrix.D 4)) := Classical.decEq _

theorem fixedRootGenerated_le_of_simple_parameters (q : CFSG.PrimePower)
    (H : Subgroup (Matrix GeckIndex GeckIndex (q.Extension 3))ˣ)
    (hshort : ∀neg t,shortOrbit (q.Extension 3) (definingFieldAutomorphism q 3) neg t∈H)
    (hmiddle : ∀(neg:Bool) (t:fixedField q),canonicalRoot rawData (q.Extension 3) neg 1 t.val∈H) :
    fixedRootGenerated (q.Extension 3) (definingFieldAutomorphism q 3)≤H := by
  have hshortW : CFSGTrialityGeckFixedRootWords.shortWeyl (q.Extension 3)∈H := by
    have he := orbit_word_parameter (q.Extension 3) (definingFieldAutomorphism q 3) false
    change CFSGTrialityGeckFixedRootWords.shortWeyl (q.Extension 3)=
      shortOrbit (q.Extension 3) (definingFieldAutomorphism q 3) false 1*
      shortOrbit (q.Extension 3) (definingFieldAutomorphism q 3) true (-1)*
      shortOrbit (q.Extension 3) (definingFieldAutomorphism q 3) false 1 at he
    rw [he]
    exact H.mul_mem (H.mul_mem (hshort false 1) (hshort true (-1))) (hshort false 1)
  have hlongW : longWeyl (q.Extension 3)∈H := by
    have he := orbit_word_parameter (q.Extension 3) (definingFieldAutomorphism q 3) true
    change longWeyl (q.Extension 3)=canonicalRoot rawData (q.Extension 3) false 1 1*
      canonicalRoot rawData (q.Extension 3) true 1 (-1)*canonicalRoot rawData (q.Extension 3) false 1 1 at he
    rw [he]
    exact H.mul_mem (H.mul_mem (hmiddle false 1) (hmiddle true (-1))) (hmiddle false 1)
  have hshortT (s:Fin 3) : shortTransport (q.Extension 3) s∈H := by
    fin_cases s
    · exact H.one_mem
    · exact hlongW
    · exact H.mul_mem hshortW hlongW
  have hlongT (s:Fin 3) : longTransport (q.Extension 3) s∈H := by
    fin_cases s
    · exact H.one_mem
    · exact hshortW
    · exact H.mul_mem hlongW hshortW
  have hshortS (s:Fin 3) (t:q.Extension 3) :
      shortSection (q.Extension 3) (definingFieldAutomorphism q 3) s false t∈H :=
    H.mul_mem (H.mul_mem (hshortT s) (hshort false t)) (H.inv_mem (hshortT s))
  have hlongS (s:Fin 3) (t:fixedField q) : longSection (q.Extension 3) s false t.val∈H :=
    H.mul_mem (H.mul_mem (hlongT s) (hmiddle false t)) (H.inv_mem (hlongT s))
  have hsections : sectionGenerated (q.Extension 3) (definingFieldAutomorphism q 3)≤
      H.comap (PositiveGroup (q.Extension 3)).subtype := by
    apply (Subgroup.closure_le _).mpr
    rintro _ (⟨s,t,ht,rfl⟩|⟨s,t,_,rfl⟩)
    · change (longPositiveSection (q.Extension 3) s t).val∈H
      rw [longPositiveSection_val]
      exact hlongS s ⟨t.toAdd,ht⟩
    · change (shortPositiveSection (q.Extension 3) (definingFieldAutomorphism q 3) s t).val∈H
      rw [shortPositiveSection_val]
      exact hshortS s t.toAdd
  have hpositive : signedFixed (q.Extension 3) (definingFieldAutomorphism q 3) false≤H := by
    intro u hu
    let v : PositiveGroup (q.Extension 3) := ⟨u,hu.1⟩
    have hvfix : positiveTwist (q.Extension 3) (definingFieldAutomorphism q 3) v=v := by
      apply Subtype.ext
      exact (positiveTwist_val (q.Extension 3) (definingFieldAutomorphism q 3) v).trans hu.2
    have hv : v∈fixedPositive (q.Extension 3) (definingFieldAutomorphism q 3) := hvfix
    rw [fixedPositive_eq_sectionGenerated] at hv
    exact hsections hv
  have hword (r:List Bool) : CFSGNormTwoGeckWeylWordDegree.wordUnit (CartanMatrix.D 4)
      (CartanMatrix.D_transpose 4) D4_positive_definite Base Index (q.Extension 3) (expandRelative r)∈H := by
    induction r with
    | nil => exact H.one_mem
    | cons a r ih =>
      cases a
      · rw [expandRelative,wordUnit_append]
        apply H.mul_mem _ ih
        simpa only [word_eq_canonicalWord,CFSGTrialityGeckFixedRootWords.shortWeyl] using hshortW
      · rw [expandRelative,wordUnit_append]
        apply H.mul_mem _ ih
        simpa only [word_eq_canonicalWord,longWeyl] using hlongW
  have hO : relativeOpposition (q.Extension 3)∈H := hword oppositionRelativeWord
  have hnegative : signedFixed (q.Extension 3) (definingFieldAutomorphism q 3) true≤H := by
    rw [←fixed_positive_image_eq_fixed_negative]
    rintro _ ⟨u,hu,rfl⟩
    exact H.mul_mem (H.mul_mem hO (hpositive hu)) (H.inv_mem hO)
  exact sup_le hpositive hnegative

def simpleSignedGenerators (q : CFSG.PrimePower) : Set (Matrix GeckIndex GeckIndex (q.Extension 3))ˣ :=
  {x|∃(neg:Bool) (t:q.Extension 3),x=shortOrbit (q.Extension 3) (definingFieldAutomorphism q 3) neg t}∪
  {x|∃(neg:Bool) (t:fixedField q),x=canonicalRoot rawData (q.Extension 3) neg 1 t.val}

theorem simpleSignedGenerators_closure (q : CFSG.PrimePower) :
    Subgroup.closure (simpleSignedGenerators q)=
      fixedRootGenerated (q.Extension 3) (definingFieldAutomorphism q 3) := by
  apply le_antisymm
  · apply (Subgroup.closure_le _).mpr
    rintro x (⟨neg,t,rfl⟩|⟨neg,t,rfl⟩)
    · exact shortOrbit_mem_generated _ _ neg t
        (CFSGTrialityTripleFixedRoots.extension_three_pow_thrice q t)
    · exact central_root_mem_generated _ _ neg t.val t.property
  · apply fixedRootGenerated_le_of_simple_parameters
    · intro neg t
      exact Subgroup.subset_closure (Or.inl ⟨neg,t,rfl⟩)
    · intro neg t
      exact Subgroup.subset_closure (Or.inr ⟨neg,t,rfl⟩)

end SymmetricSubgroupAsymptotics.CFSGTrialityGeckSimpleSignedGeneration
