import SymmetricSubgroupAsymptotics.CFSGFFourE6RelativeWords
import SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckSectionRootParameters
import SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckSectionDiagramLabels

/-! Both kinds of diagram-orbit seed are literal folded F4 roots. Their
relative-word conjugators also lie in F4, over the SAME coefficient field.
These are matrix subgroup witnesses, without original-source injectivity. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGFFourE6RootSeeds
open CFSGFFourSerreMatrices CFSGFFourE6PositiveRootUnits CFSGFFourE6NegativeRootUnits
open CFSGFFourE6RelativeWords CFSGSerreQuadraticMatrix CFSGSerreQuadraticWeylWord
open CFSGNormTwoGeckOrthogonalWeyl CFSGExceptionalNormTwoBases CFSGExceptionalCartanPositiveDefinite
open CFSGSerreDiagram CFSGTwistedE6GeckOriginalRootSections
open CFSGTwistedE6GeckSectionRootParameters CFSGNormTwoGeckIntegralWord
open CFSGNormTwoGeckWeylWordAlgebra CFSGTwistedE6FixedWordClassification

theorem singleton_seed_mem (K : Type) [Field K] (j : Fin 6)
    (hj : e6Permutation j=j) (t : K) :
    canonicalRoot e6Data K true j t ∈ canonicalElementaryGroup realizationData K := by
  have hr (i : Fin 4) : canonicalRoot realizationData K true i t ∈
      canonicalElementaryGroup realizationData K := Subgroup.subset_closure ⟨true,i,t,rfl⟩
  fin_cases j
  · change (5 : Fin 6)=0 at hj
    exact False.elim ((by decide : (5 : Fin 6)≠0) hj)
  · have h := hr 3
    rw [folded_negative_root] at h
    change canonicalRoot e6Data K true 1 t ∈ _ at h
    exact h
  · change (4 : Fin 6)=2 at hj
    exact False.elim ((by decide : (4 : Fin 6)≠2) hj)
  · have h := hr 2
    rw [folded_negative_root] at h
    change canonicalRoot e6Data K true 3 t ∈ _ at h
    exact h
  · change (2 : Fin 6)=4 at hj
    exact False.elim ((by decide : (2 : Fin 6)≠4) hj)
  · change (0 : Fin 6)=5 at hj
    exact False.elim ((by decide : (0 : Fin 6)≠5) hj)

theorem paired_seed_mem (K : Type) [Field K] (j : Fin 6)
    (hj : e6Permutation j≠j) (t : K) :
    canonicalRoot e6Data K true j t * canonicalRoot e6Data K true (e6Permutation j) t ∈
      canonicalElementaryGroup realizationData K := by
  have hr (i : Fin 4) : canonicalRoot realizationData K true i t ∈
      canonicalElementaryGroup realizationData K := Subgroup.subset_closure ⟨true,i,t,rfl⟩
  have h0 := hr 0
  rw [folded_negative_root] at h0
  change canonicalRoot e6Data K true 0 t * canonicalRoot e6Data K true 5 t ∈ _ at h0
  have h1 := hr 1
  rw [folded_negative_root] at h1
  change canonicalRoot e6Data K true 2 t * canonicalRoot e6Data K true 4 t ∈ _ at h1
  fin_cases j
  · change canonicalRoot e6Data K true 0 t * canonicalRoot e6Data K true 5 t ∈ _
    exact h0
  · change (1 : Fin 6)≠1 at hj
    exact False.elim (hj rfl)
  · change canonicalRoot e6Data K true 2 t * canonicalRoot e6Data K true 4 t ∈ _
    exact h1
  · change (3 : Fin 6)≠3 at hj
    exact False.elim (hj rfl)
  · have hc := (orthogonal_signed_roots CartanMatrix.E₆ CartanMatrix.E₆_transpose
      E6_positive_definite E6Base E6Index K 2 4 (by rw [E6_cartan];decide) true true t t).eq
    change canonicalRoot e6Data K true 4 t * canonicalRoot e6Data K true 2 t ∈ _
    rw [←hc]
    exact h1
  · have hc := (orthogonal_signed_roots CartanMatrix.E₆ CartanMatrix.E₆_transpose
      E6_positive_definite E6Base E6Index K 0 5 (by rw [E6_cartan];decide) true true t t).eq
    change canonicalRoot e6Data K true 5 t * canonicalRoot e6Data K true 0 t ∈ _
    rw [←hc]
    exact h0

def sectionTransport (K : Type) [Field K] (k : PositiveRoot) : (Matrix Index Index K)ˣ :=
  (canonicalWord e6Data K (expandRelative (sectionRelative k)))⁻¹

theorem sectionTransport_mem (K : Type) [Field K] (k : PositiveRoot) :
    sectionTransport K k ∈ canonicalElementaryGroup realizationData K :=
  (canonicalElementaryGroup realizationData K).inv_mem
    (relativeWord_mem_folded K (sectionRelative k))

theorem sectionTransport_eq_word (K : Type) [Field K] (k : PositiveRoot) :
    sectionTransport K k = canonicalWord e6Data K (sectionWord k) := by
  have hi := wordUnit_inverseWord CartanMatrix.E₆ CartanMatrix.E₆_transpose E6_positive_definite
    E6Base E6Index K (expandRelative (sectionRelative k))
  simpa only [sectionTransport,sectionWord,word_eq_canonicalWord] using hi.symm

theorem conjugated_seed_eq_parameter (K : Type) [Field K] (k : PositiveRoot) (t : K) :
    sectionTransport K k * canonicalRoot e6Data K true (sectionNode k) t *
      (sectionTransport K k)⁻¹ = (sectionParameter K k t).val := by
  rw [sectionTransport_eq_word]
  rfl

end SymmetricSubgroupAsymptotics.CFSGFFourE6RootSeeds
