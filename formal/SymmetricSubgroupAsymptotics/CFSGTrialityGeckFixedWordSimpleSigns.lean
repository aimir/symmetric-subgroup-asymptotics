import SymmetricSubgroupAsymptotics.CFSGTrialityGeckFixedPositiveRaw
import SymmetricSubgroupAsymptotics.CFSGTrialityGeckRelativeSimpleSigns
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateNegativeSimpleWord
import SymmetricSubgroupAsymptotics.CFSGTrialityGeckShortOrbitCommutator

/-! Two literal fixed root tests detect a non-opposite relative Weyl
cell. The outer test is the whole short Frobenius-orbit word, so no
individual outer root is incorrectly assumed fixed, including q=2. -/
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTrialityGeckFixedWordSimpleSigns
open CFSGTrialityGeckFixedPositiveRaw CFSGTrialityGeckRelativeSimpleSigns
open CFSGTrialityGeckShortCentralizerCardinality CFSGTrialityGeckFixedPositiveGeneration
open CFSGTrialityGeckFixedRootWords CFSGTrialityGeckFixedRootSections
open CFSGTrialityGeckSectionQuotientCoordinates CFSGTrialityGeckPositiveTwist
open CFSGTrialityGeckDiagramCovariance CFSGTrialityD4NormTwo CFSGTrialityRelativeWordLanguage
open CFSGTrialityD4WordDiscriminant CFSGTrialityGeckShortOrbitCommutator
open CFSGNormTwoGeckWeylWordDegree CFSGNormTwoGeckIntegralRealization
open CFSGNormTwoCoordinateWeylRootMembership CFSGNormTwoGeckOppositeIntersection
open CFSGNormTwoCoordinateHeight CFSGNormTwoCoordinateNegativeSimpleWord
open CFSGSerreOrdinaryTwists CFSGSerreQuadraticMatrix
local notation "A" => CartanMatrix.D 4
local notation "hd" => CartanMatrix.D_diag 4
local notation "hs" => CartanMatrix.D_transpose 4
local notation "hp" => D4_positive_definite
local notation "ho" => CartanMatrix.D_off_diag_nonpos 4
local instance : DecidableEq (CFSGNormTwoRootPairing.Roots A) := Classical.decEq _

private theorem source_eq_one_of_disjoint {G : Type*} [Group G]
    (H : Subgroup G) (g x : G) (hx : x∈H) (hgx : g*x*g⁻¹∈H)
    (hdisjoint : H⊓H.map (MulAut.conj g).toMonoidHom=⊥) : x=1 := by
  have hm : g*x*g⁻¹∈H⊓H.map (MulAut.conj g).toMonoidHom := ⟨hgx,⟨x,hx,rfl⟩⟩
  rw [hdisjoint,Subgroup.mem_bot] at hm
  apply (MulAut.conj g).injective
  exact hm.trans (map_one (MulAut.conj g)).symm

theorem shortOrbit_mem_fixedPositiveRaw (q : CFSG.PrimePower) (t : q.Extension 3) :
    shortOrbit (q.Extension 3) (definingFieldAutomorphism q 3) false t∈fixedPositiveRaw q := by
  refine ⟨shortFixedElement (q.Extension 3) (definingFieldAutomorphism q 3)
    (CFSGTrialityTripleFixedRoots.extension_three_pow_thrice q) 0 t,?_⟩
  rw [shortFixedElement_val]
  simp only [shortSection,shortTransport,Matrix.cons_val_zero,inv_one,one_mul,mul_one]

theorem middleRoot_mem_fixedPositiveRaw (q : CFSG.PrimePower) :
    canonicalRoot rawData (q.Extension 3) false 1 1∈fixedPositiveRaw q := by
  let z : fixedPositive (q.Extension 3) (definingFieldAutomorphism q 3) :=
    ⟨longPositiveSection (q.Extension 3) 0 (Multiplicative.ofAdd 1),
      longPositiveSection_fixed (q.Extension 3) (definingFieldAutomorphism q 3) 0
        (Multiplicative.ofAdd 1) (map_one _)⟩
  refine ⟨z,?_⟩
  change (longPositiveSection (q.Extension 3) 0 (Multiplicative.ofAdd 1)).val=_
  rw [longPositiveSection_val]
  change (1 : (Matrix GeckIndex GeckIndex (q.Extension 3))ˣ)*
    canonicalRoot rawData (q.Extension 3) false 1 1*1⁻¹=
      canonicalRoot rawData (q.Extension 3) false 1 1
  simp only [inv_one,one_mul,mul_one]

private theorem positive_conjugate_short (q : CFSG.PrimePower) (r : List Bool)
    (hpos : ∀i,0≤(rootAction (expandRelative r) (Index 0)).val i) :
    (wordUnit A hs hp Base Index (q.Extension 3) (expandRelative r))*
      shortOrbit (q.Extension 3) (definingFieldAutomorphism q 3) false 1*
        (wordUnit A hs hp Base Index (q.Extension 3) (expandRelative r))⁻¹∈Positive (q.Extension 3) := by
  let W := wordUnit A hs hp Base Index (q.Extension 3) (expandRelative r)
  have hall := relative_outer_images_nonnegative r hpos
  change (MulAut.conj W) (shortOrbit (q.Extension 3) (definingFieldAutomorphism q 3) false 1)∈_
  change (MulAut.conj W) (canonicalRoot rawData (q.Extension 3) false 0 1*
    canonicalRoot rawData (q.Extension 3) false 2 (definingFieldAutomorphism q 3 1)*
    canonicalRoot rawData (q.Extension 3) false 3
      (definingFieldAutomorphism q 3 (definingFieldAutomorphism q 3 1)))∈_
  rw [map_mul,map_mul]
  exact (Positive (q.Extension 3)).mul_mem
    ((Positive (q.Extension 3)).mul_mem
      (positive_word_mem A hd hs hp ho (q.Extension 3) (expandRelative r) 0 1
        (hall 0 (by decide)))
      (positive_word_mem A hd hs hp ho (q.Extension 3) (expandRelative r) 2
        (definingFieldAutomorphism q 3 1) (hall 2 (by decide))))
    (positive_word_mem A hd hs hp ho (q.Extension 3) (expandRelative r) 3
      (definingFieldAutomorphism q 3 (definingFieldAutomorphism q 3 1)) (hall 3 (by decide)))

theorem relative_simple_nonpositive_of_fixed_disjoint (q : CFSG.PrimePower) (r : List Bool)
    (hdisj : fixedPositiveRaw q⊓(fixedPositiveRaw q).map
      (MulAut.conj (wordUnit A hs hp Base Index (q.Extension 3) (expandRelative r))).toMonoidHom=⊥)
    (i : Fin 4) : ∀l,(rootAction (expandRelative r) (Index i)).val l≤0 := by
  let W := wordUnit A hs hp Base Index (q.Extension 3) (expandRelative r)
  have h0 : ∀l,(rootAction (expandRelative r) (Index 0)).val l≤0 := by
    rcases word_sign_membership A hd hs hp ho (q.Extension 3) (expandRelative r) 0 1 with hpos|hneg
    · have hconj := relative_conjugate_mem_of_positive q r _ (shortOrbit_mem_fixedPositiveRaw q 1)
        (positive_conjugate_short q r hpos.1)
      have he := source_eq_one_of_disjoint (fixedPositiveRaw q) W _
        (shortOrbit_mem_fixedPositiveRaw q 1) hconj hdisj
      have hzero := shortOrbit_zero (q.Extension 3) (definingFieldAutomorphism q 3) false
      have hz := shortOrbit_injective (q.Extension 3) (definingFieldAutomorphism q 3)
        (he.trans hzero.symm)
      exact False.elim (one_ne_zero hz)
    · exact hneg.1
  have h1 : ∀l,(rootAction (expandRelative r) (Index 1)).val l≤0 := by
    rcases word_sign_membership A hd hs hp ho (q.Extension 3) (expandRelative r) 1 1 with hpos|hneg
    · have hconj := relative_conjugate_mem_of_positive q r _ (middleRoot_mem_fixedPositiveRaw q) hpos.2
      have he := source_eq_one_of_disjoint (fixedPositiveRaw q) W _
        (middleRoot_mem_fixedPositiveRaw q) hconj hdisj
      exact False.elim (canonicalRoot_one_ne_one A hs hp Base Index coordinateHeight
        (simple_height A hd hs hp ho) (q.Extension 3) 1 he)
    · exact hneg.1
  exact relative_simple_images_nonpositive r h0 h1 i

end SymmetricSubgroupAsymptotics.CFSGTrialityGeckFixedWordSimpleSigns
