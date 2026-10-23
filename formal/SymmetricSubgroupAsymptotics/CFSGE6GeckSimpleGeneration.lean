import SymmetricSubgroupAsymptotics.CFSGE6GeckSimpleGenerationSeeds
import SymmetricSubgroupAsymptotics.CFSGE6GeckFixedHeightGeneration
import SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckRelativeOpposition

/-! The four signed simple charts genuinely generate the actual fixed
root group. Their constructed relative conjugators supply every local
root section; fixed-height peeling supplies all of fixed U, and literal
relative opposition supplies fixed V. No generation callback is used. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGE6GeckSimpleGeneration
open CFSGE6GeckSimpleGenerationSeeds CFSGE6GeckFixedHeightGeneration
open CFSGE6GeckFixedSimpleParameters CFSGE6GeckSignedSimpleParameters
open CFSGTwistedE6GeckSectionRootParameters CFSGTwistedE6GeckOriginalRootSections
open CFSGTwistedE6GeckSectionDiagramLabels CFSGTwistedE6WeylChamber
open CFSGTwistedE6GeckRelativeRootGenerated CFSGTwistedE6GeckMatrixTwist
open CFSGTwistedE6GeckPositiveTwist CFSGTwistedE6GeckPositiveCoordinateLifts
open CFSGTwistedE6GeckDiagramCovariance CFSGTwistedE6GeckRelativeOpposition
open CFSGSerreQuadraticMatrix CFSGSerreDiagram CFSGTwistedE6RelativeOppositionLattice
variable (K : Type) [Field K] [Finite K] (sigma : RingAut K)
    (S : Subgroup ((Matrix GeckIndex GeckIndex K)ˣ))
    (hsingle : ∀neg j (a : fixedCoefficient K sigma),rawSingletonHom K neg j (Multiplicative.ofAdd (a : K))∈S)
    (hpair : ∀neg j (a : K),rawPairedHom K sigma neg j (Multiplicative.ofAdd a)∈S)

omit [Finite K] in
theorem sectionParameter_twist (k : PositiveRoot) (a : K) :
    unitTwist K sigma (sectionParameter K k a).val=
      sectionConjugator K k*canonicalRoot rawData K true (CFSG.Models.e6Twist (sectionNode k)) (sigma a)*
        (sectionConjugator K k)⁻¹ := by
  rw [sectionParameter_val_conjugate,map_mul,map_mul,map_inv,sectionConjugator_fixed,unitTwist_root]
  rfl

include hsingle hpair in
theorem singleton_section_mem (k : PositiveRoot) (hk : diagramRoot k.val=k.val)
    (x : RootLine K k.val) (hx : unitTwist K sigma x.val=x.val) : (rootLinePositive K k x).val∈S := by
  obtain ⟨a,ha⟩ := (sectionParameterMulEquiv K k).surjective x
  have ht : unitTwist K sigma (sectionParameter K k a.toAdd).val=(sectionParameter K k a.toAdd).val := by
    change unitTwist K sigma ((sectionParameterMulEquiv K k) a).val=((sectionParameterMulEquiv K k) a).val
    rw [ha]
    exact hx
  have hj := (section_seed_fixed_iff k).mpr hk
  rw [sectionParameter_twist,sectionParameter_val_conjugate,hj] at ht
  have hroot : canonicalRoot rawData K true (sectionNode k) (sigma a.toAdd)=
      canonicalRoot rawData K true (sectionNode k) a.toAdd :=
    (MulAut.conj (sectionConjugator K k)).injective ht
  have hscalar : sigma a.toAdd=a.toAdd :=
    congrArg Multiplicative.toAdd (rawSimple_injective K true (sectionNode k) hroot)
  change x.val∈S
  rw [←ha]
  change (sectionParameter K k a.toAdd).val∈S
  rw [sectionParameter_val_conjugate]
  exact S.mul_mem (S.mul_mem (sectionConjugator_mem K sigma S hsingle hpair k)
    (fixed_simple_seed_mem K sigma S hsingle true (sectionNode k) hj a.toAdd hscalar))
    (S.inv_mem (sectionConjugator_mem K sigma S hsingle hpair k))

include hsingle hpair in
theorem paired_section_mem (hsigma : Function.Involutive sigma)
    (k : PositiveRoot) (hk : diagramRoot k.val≠k.val) (x : RootLine K k.val) :
    (rootLinePositive K k x*positiveTwist K sigma (rootLinePositive K k x)).val∈S := by
  obtain ⟨a,ha⟩ := (sectionParameterMulEquiv K k).surjective x
  have hj : CFSG.Models.e6Twist (sectionNode k)≠sectionNode k :=
    fun h=>hk ((section_seed_fixed_iff k).mp h)
  let z : (Matrix GeckIndex GeckIndex K)ˣ := x.val
  have hz : z=(sectionParameter K k a.toAdd).val := by
    change x.val=((sectionParameterMulEquiv K k) a).val
    exact (congrArg Subtype.val ha).symm
  have he : z*unitTwist K sigma z=
      sectionConjugator K k*(canonicalRoot rawData K true (sectionNode k) a.toAdd*
        canonicalRoot rawData K true (CFSG.Models.e6Twist (sectionNode k)) (sigma a.toAdd))*
      (sectionConjugator K k)⁻¹ := by
    rw [hz,sectionParameter_twist,sectionParameter_val_conjugate]
    group
  change z*unitTwist K sigma z∈S
  rw [he]
  exact S.mul_mem (S.mul_mem (sectionConjugator_mem K sigma S hsingle hpair k)
    (nonfixed_simple_pair_mem K sigma S hpair hsigma true (sectionNode k) hj a.toAdd))
    (S.inv_mem (sectionConjugator_mem K sigma S hsingle hpair k))

include hsingle hpair in
theorem fixed_positive_le_of_simple_charts (hsigma : Function.Involutive sigma)
    (hSfixed : ∀u∈S,unitTwist K sigma u=u) : signedFixed K sigma false≤S := by
  intro u hu
  let T := S.subgroupOf (Positive K)
  let x : Positive K := ⟨u,hu.1⟩
  have hT : ∀a∈T,positiveTwist K sigma a=a := by
    intro a ha
    apply Subtype.ext
    exact hSfixed a.val ha
  have hx : x∈T := fixed_mem_of_root_sections K sigma T hT
    (singleton_section_mem K sigma S hsingle hpair)
    (paired_section_mem K sigma S hsingle hpair hsigma) x (Subtype.ext hu.2)
  exact hx

include hsingle hpair in
theorem generated_le_of_simple_charts (hsigma : Function.Involutive sigma)
    (hSfixed : ∀u∈S,unitTwist K sigma u=u) : fixedRootGenerated K sigma≤S := by
  have hU := fixed_positive_le_of_simple_charts K sigma S hsingle hpair hsigma hSfixed
  have hW : relativeOpposition K∈S := by
    exact relative_word_mem K sigma S hsingle hpair oppositionRelativeWord
  apply sup_le hU
  rw [←fixed_positive_image_eq_fixed_negative K sigma]
  rintro _ ⟨u,hu,rfl⟩
  change relativeOpposition K*u*(relativeOpposition K)⁻¹∈S
  exact S.mul_mem (S.mul_mem hW (hU hu)) (S.inv_mem hW)

end SymmetricSubgroupAsymptotics.CFSGE6GeckSimpleGeneration
