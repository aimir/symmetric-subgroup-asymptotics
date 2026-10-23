import SymmetricSubgroupAsymptotics.CFSGFFourE6RootSeeds
import SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckRelativeWordTwist
import SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckRootCoordinateLifts

/-! Every singleton root line, and every paired diagram-orbit product,
has a literal folded F4 matrix witness. All parameters are in K and the
coefficient twist is IDENTITY; no extension-field fixed-source theorem
is specialized without checking its hypotheses. -/
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGFFourE6PositiveSections
open CFSGFFourSerreMatrices CFSGFFourE6PositiveRootUnits CFSGFFourE6RootSeeds
open CFSGTwistedE6GeckOriginalRootSections CFSGTwistedE6GeckSectionRootParameters
open CFSGTwistedE6GeckSectionDiagramLabels CFSGTwistedE6GeckRelativeWordTwist
open CFSGTwistedE6GeckMatrixTwist CFSGTwistedE6GeckDiagramCovariance
open CFSGTwistedE6WeylChamber CFSGSerreQuadraticMatrix CFSGSerreDiagram

local instance positiveSectionRootDecEq : DecidableEq
    (CFSGNormTwoRootPairing.Roots CartanMatrix.E₆) := Classical.decEq _

def rawRootUnit (K : Type) [Field K] (k : PositiveRoot) (x : RootLine K k.val) :
    (Matrix GeckIndex GeckIndex K)ˣ :=
  (CFSGTwistedE6GeckRootCoordinateLifts.rootLineToMatrix K k.val x).val

theorem rawRootUnit_eq (K : Type) [Field K] (k : PositiveRoot) (x : RootLine K k.val) :
    rawRootUnit K k x=x.val := rfl

private theorem sectionParameter_surjective (K : Type) [Field K] [Finite K] (k : PositiveRoot) :
    Function.Surjective (sectionParameter K k) := by
  intro x
  obtain ⟨t,ht⟩ := (sectionParameterMulEquiv K k).surjective x
  exact ⟨t.toAdd,ht⟩

theorem sectionTransport_fixed (K : Type) [Field K] (k : PositiveRoot) :
    unitTwist K (RingEquiv.refl K) (sectionTransport K k)=sectionTransport K k := by
  change unitTwist K (RingEquiv.refl K)
    (CFSGSerreQuadraticWeylWord.canonicalWord e6Data K
      (CFSGTwistedE6FixedWordClassification.expandRelative (sectionRelative k)))⁻¹ = _
  rw [map_inv,relative_word_fixed]
  rfl

theorem singleton_root_mem_folded (K : Type) [Field K] [Finite K] (k : PositiveRoot)
    (hk : diagramRoot k.val=k.val) (x : RootLine K k.val) :
    x.val ∈ canonicalElementaryGroup realizationData K := by
  obtain ⟨t,rfl⟩ := sectionParameter_surjective K k x
  have hj : e6Permutation (sectionNode k)=sectionNode k := (section_seed_fixed_iff k).mpr hk
  rw [←conjugated_seed_eq_parameter]
  exact (canonicalElementaryGroup realizationData K).mul_mem
    ((canonicalElementaryGroup realizationData K).mul_mem (sectionTransport_mem K k)
      (singleton_seed_mem K (sectionNode k) hj t))
    ((canonicalElementaryGroup realizationData K).inv_mem (sectionTransport_mem K k))

theorem sectionParameter_twist (K : Type) [Field K] (k : PositiveRoot) (t : K) :
    unitTwist K (RingEquiv.refl K) (sectionParameter K k t).val =
      sectionTransport K k * canonicalRoot e6Data K true (e6Permutation (sectionNode k)) t *
        (sectionTransport K k)⁻¹ := by
  rw [←conjugated_seed_eq_parameter,map_mul,map_mul,map_inv,
    sectionTransport_fixed,unitTwist_root]
  rfl

theorem paired_root_mem_folded (K : Type) [Field K] [Finite K] (k : PositiveRoot)
    (hk : diagramRoot k.val≠k.val) (x : RootLine K k.val) :
    rawRootUnit K k x * unitTwist K (RingEquiv.refl K) (rawRootUnit K k x) ∈
      canonicalElementaryGroup realizationData K := by
  obtain ⟨t,rfl⟩ := sectionParameter_surjective K k x
  have hj : e6Permutation (sectionNode k)≠sectionNode k := by
    intro he
    exact hk ((section_seed_fixed_iff k).mp he)
  have hp := paired_seed_mem K (sectionNode k) hj t
  have hm : sectionTransport K k *
      (canonicalRoot e6Data K true (sectionNode k) t *
        canonicalRoot e6Data K true (e6Permutation (sectionNode k)) t) *
      (sectionTransport K k)⁻¹ ∈ canonicalElementaryGroup realizationData K :=
    (canonicalElementaryGroup realizationData K).mul_mem
      ((canonicalElementaryGroup realizationData K).mul_mem (sectionTransport_mem K k) hp)
      ((canonicalElementaryGroup realizationData K).inv_mem (sectionTransport_mem K k))
  have he : rawRootUnit K k (sectionParameter K k t) *
      unitTwist K (RingEquiv.refl K) (rawRootUnit K k (sectionParameter K k t)) =
      sectionTransport K k *
        (canonicalRoot e6Data K true (sectionNode k) t *
          canonicalRoot e6Data K true (e6Permutation (sectionNode k)) t) *
        (sectionTransport K k)⁻¹ := by
    simp only [rawRootUnit_eq]
    rw [sectionParameter_twist,←conjugated_seed_eq_parameter]
    group
  exact he.symm ▸ hm

end SymmetricSubgroupAsymptotics.CFSGFFourE6PositiveSections
