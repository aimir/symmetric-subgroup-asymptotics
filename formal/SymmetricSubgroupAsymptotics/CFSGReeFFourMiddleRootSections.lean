import SymmetricSubgroupAsymptotics.CFSGGroupLabelSubgroupTransport
import SymmetricSubgroupAsymptotics.CFSGReeFFourMiddlePositiveGenerators
import SymmetricSubgroupAsymptotics.CFSGE6GeckMiddleRootSupport
import SymmetricSubgroupAsymptotics.CFSGE6GeckPairedWordRootSections
import SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckRelativeWordTwist
import SymmetricSubgroupAsymptotics.CFSGTwistedE6DiagramRootOrthogonality

/-! Every fixed singleton or paired section on the six middle A3 roots
belongs to the literal ordinary four-parameter middle subgroup. All
parameters are obtained through actual root-line conjugation. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical Matrix
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourMiddleRootSections
open CFSGReeFFourMiddlePositiveGenerators CFSGReeFFourMiddlePositiveSubgroup
open CFSGReeFFourFieldParameters CFSGE6GeckMiddleRootSupport CFSGE6GeckMiddleRootDegrees
open CFSGE6GeckPositiveWordRootSections CFSGE6GeckPairedWordRootSections
open CFSGTwistedE6GeckSectionRootParameters CFSGTwistedE6GeckOriginalRootSections
open CFSGTwistedE6GeckDiagramCovariance CFSGTwistedE6GeckMatrixTwist
open CFSGTwistedE6GeckPositiveTwist CFSGTwistedE6WeylChamber
open CFSGTwistedE6GeckRelativeWordTwist CFSGTwistedE6DiagramRootOrthogonality
open CFSGE6GeckMiddleHigherLeading CFSGE6GeckMiddleFactorInjective
open CFSGE6GeckMiddleAThreeCollecting CFSGNormTwoGeckOrthogonalWeyl
open CFSGExceptionalNormTwoBases CFSGExceptionalCartanPositiveDefinite CFSGNormTwoRootPairing
open CFSGNormTwoGeckWeylWordDegree CFSGSerreQuadraticMatrix CFSGSerreQuadraticWeylWord
open CFSGSerreDiagram CFSGNormTwoCoordinateLeadingHom
local notation "A" => CartanMatrix.E₆
local notation "hd" => CartanMatrix.E₆_diag
local notation "hs" => CartanMatrix.E₆_transpose
local notation "hp" => E6_positive_definite
local notation "ho" => CartanMatrix.E₆_off_diag_nonpos
local instance : DecidableEq (Roots A) := Classical.decEq _

private def wordAt : Fin 6 → List (Fin 6) := ![[],[],[],[3],[3],[2,4]]
private def nodeAt : Fin 6 → Fin 6 := ![2,3,4,2,4,3]
private def rootAt (i : Fin 6) : Roots A :=
  wordRoot A hs hp E6Base E6Index (wordAt i) (E6Index (nodeAt i))

private theorem rootAt_val (i : Fin 6) : (rootAt i).val = middleVector i := by
  fin_cases i
  · change (Pi.single (2 : Fin 6) (1 : ℤ)) = ![0,0,1,0,0,0]
    decide +kernel
  · change (Pi.single (3 : Fin 6) (1 : ℤ)) = ![0,0,0,1,0,0]
    decide +kernel
  · change (Pi.single (4 : Fin 6) (1 : ℤ)) = ![0,0,0,0,1,0]
    decide +kernel
  · exact paired_first_degree
  · exact paired_second_degree
  · exact highest_root_degree

private theorem vector_fixed_iff (i : Fin 6) :
    (∀ j, middleVector i (e6Permutation j) = middleVector i j) ↔ i=1 ∨ i=5 := by
  revert i
  decide +kernel

private theorem rootAt_fixed_iff (i : Fin 6) :
    diagramRoot (rootAt i) = rootAt i ↔ i=1 ∨ i=5 := by
  constructor
  · intro h
    apply (vector_fixed_iff i).mp
    intro j
    have he := congrArg (fun k : Roots A => k.val j) h
    change (diagramRoot (rootAt i)).val j = (rootAt i).val j at he
    simpa only [diagramRoot_coordinate,rootAt_val] using he
  · intro h
    apply Subtype.ext
    funext j
    rw [diagramRoot_coordinate,rootAt_val]
    exact (vector_fixed_iff i).mpr h j

private abbrev rawMiddle (m : ℕ) :=
  (middlePositiveSubgroup m).map (Positive (Field m)).subtype

private theorem pair_section_mem (m : ℕ) (w : List (Fin 6)) (hw : w=[] ∨ w=[3])
    (i : Fin 6) (hi : i=2 ∨ i=4)
    (x : RootLine (Field m) (wordRoot A hs hp E6Base E6Index w (E6Index i))) :
    rawSectionValue (Field m) _ x *
      unitTwist (Field m) (RingEquiv.refl (Field m)) (rawSectionValue (Field m) _ x) ∈ rawMiddle m := by
  have hfixed : unitTwist (Field m) (RingEquiv.refl (Field m))
      (canonicalWord rawData (Field m) w) = canonicalWord rawData (Field m) w := by
    rcases hw with rfl | rfl
    · exact (unitTwist (Field m) (RingEquiv.refl (Field m))).map_one
    · exact orbit_word_fixed (Field m) (RingEquiv.refl (Field m)) 2
  obtain ⟨a,ha⟩ := exists_paired_word_parameter (Field m) w i hfixed x
  have hseed : canonicalRoot rawData (Field m) false i a *
      canonicalRoot rawData (Field m) false (e6Permutation i) a =
      canonicalRoot rawData (Field m) false 2 a * canonicalRoot rawData (Field m) false 4 a := by
    rcases hi with rfl | rfl
    · rfl
    · exact (orthogonal_signed_roots A hs hp E6Base E6Index (Field m) 4 2
        (by rw [E6_cartan]; decide) false false a a).eq
  rw [hseed] at ha
  rcases hw with rfl | rfl
  · have he : rawSectionValue (Field m) _ x *
      unitTwist (Field m) (RingEquiv.refl (Field m)) (rawSectionValue (Field m) _ x) =
        (pairedPositive (Field m) (RingEquiv.refl (Field m)) a).val := by
      simpa only [canonicalWord,one_mul,inv_one,mul_one] using ha
    exact he.symm ▸ (show (pairedPositive (Field m) (RingEquiv.refl (Field m)) a).val ∈
      rawMiddle m from ⟨_,pairedPositive_mem m a,rfl⟩)
  · have he : rawSectionValue (Field m) _ x *
      unitTwist (Field m) (RingEquiv.refl (Field m)) (rawSectionValue (Field m) _ x) =
        (pairedHigherPositive (Field m) a).val := by
      simpa only [canonicalWord,mul_one] using ha
    exact he.symm ▸ (show (pairedHigherPositive (Field m) a).val ∈ rawMiddle m from
      ⟨_,pairedHigherPositive_mem m a,rfl⟩)

theorem singleton_section_mem (m : ℕ) (k : PositiveRoot)
    (hz : outsideHeight k.val.val = 0) (hk : diagramRoot k.val = k.val)
    (x : RootLine (Field m) k.val) : x.val ∈ rawMiddle m := by
  obtain ⟨i,hi⟩ := (positive_root_zero_outside_iff k).mp hz
  have hr : k.val = rootAt i := Subtype.ext (hi.trans (rootAt_val i).symm)
  have hf : i=1 ∨ i=5 := (rootAt_fixed_iff i).mp (by rw [←hr]; exact hk)
  let y : RootLine (Field m) (rootAt i) := ⟨x.val,hr ▸ x.property⟩
  rcases hf with rfl | rfl
  · obtain ⟨a,ha⟩ := exists_word_parameter (Field m) [] 3 y
    have he : (positiveRoot A hd hs hp ho (Field m) 3 a).val = x.val := by
      simpa only [canonicalWord,one_mul,inv_one,mul_one] using ha
    exact ⟨_,simplePositive_mem m a,he⟩
  · obtain ⟨a,ha⟩ := exists_word_parameter (Field m) [2,4] 3 y
    have he : (higherPositive (Field m) a).val = x.val := by
      simpa only [canonicalWord,mul_one] using ha
    exact ⟨_,higherPositive_mem m a,he⟩

private theorem nonfixed_index_cases (i : Fin 6) (hi : ¬(i=1 ∨ i=5)) :
    i=0 ∨ i=2 ∨ i=3 ∨ i=4 := by
  revert i
  decide +kernel

private def rawLine (K : Type) [_root_.Field K] (k : Roots A) :
    Subgroup ((Matrix GeckIndex GeckIndex K)ˣ) := RootLine K k

private theorem paired_section_of_root_eq (m : ℕ) (k : Roots A)
    (w : List (Fin 6)) (hw : w=[] ∨ w=[3]) (i : Fin 6) (hi : i=2 ∨ i=4)
    (hr : k = wordRoot A hs hp E6Base E6Index w (E6Index i))
    (x : (Matrix GeckIndex GeckIndex (Field m))ˣ) (hx : x∈rawLine (Field m) k) :
    x * unitTwist (Field m) (RingEquiv.refl (Field m)) x ∈ rawMiddle m := by
  apply CFSGGroupLabelSubgroupTransport.twisted_product_mem_of_label_eq
    (rawLine (Field m)) (rawMiddle m)
    (unitTwist (Field m) (RingEquiv.refl (Field m))) k
    (wordRoot A hs hp E6Base E6Index w (E6Index i)) hr _ x hx
  intro z hz
  exact pair_section_mem m w hw i hi ⟨z,hz⟩

theorem paired_section_mem (m : ℕ) (k : PositiveRoot)
    (hz : outsideHeight k.val.val = 0) (hk : diagramRoot k.val ≠ k.val)
    (x : RootLine (Field m) k.val) :
    rawSectionValue (Field m) _ x *
      unitTwist (Field m) (RingEquiv.refl (Field m)) (rawSectionValue (Field m) _ x) ∈ rawMiddle m := by
  obtain ⟨i,hi⟩ := (positive_root_zero_outside_iff k).mp hz
  have hr : k.val = rootAt i := Subtype.ext (hi.trans (rootAt_val i).symm)
  have hn : ¬(i=1 ∨ i=5) := by
    intro hf
    apply hk
    rw [hr]
    exact (rootAt_fixed_iff i).mpr hf
  rcases nonfixed_index_cases i hn with rfl | rfl | rfl | rfl
  · exact paired_section_of_root_eq m k.val [] (Or.inl rfl) 2 (Or.inl rfl) hr (rawSectionValue (Field m) _ x) x.property
  · exact paired_section_of_root_eq m k.val [] (Or.inl rfl) 4 (Or.inr rfl) hr (rawSectionValue (Field m) _ x) x.property
  · exact paired_section_of_root_eq m k.val [3] (Or.inr rfl) 2 (Or.inl rfl) hr (rawSectionValue (Field m) _ x) x.property
  · exact paired_section_of_root_eq m k.val [3] (Or.inr rfl) 4 (Or.inr rfl) hr (rawSectionValue (Field m) _ x) x.property

end SymmetricSubgroupAsymptotics.CFSGReeFFourMiddleRootSections
