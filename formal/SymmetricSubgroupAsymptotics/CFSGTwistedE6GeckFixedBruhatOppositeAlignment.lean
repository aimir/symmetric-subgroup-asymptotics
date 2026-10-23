import SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckFixedWordSimpleSigns
import SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckFixedRootFamilyCover
import SymmetricSubgroupAsymptotics.CFSGSubgroupConjugateDisjoint

/-! Genuine fixed upper matrices act transitively on their disjoint
conjugates inside the fixed E6 matrix group, for an arbitrary coefficient
automorphism. Actual relative Bruhat coordinates and fixed simple-orbit
tests supply opposition; no abstract BN-pair or fixed-group recognition
is an input. Identity coefficients include the folded F4 case. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckFixedBruhatOppositeAlignment
open CFSGTwistedE6GeckFixedWordSimpleSigns CFSGTwistedE6GeckFixedRootFamilyCover
open CFSGTwistedE6GeckCentralTwistedBruhatCell CFSGTwistedE6GeckCentralTwistedCellFactors
open CFSGTwistedE6GeckRelativeRootGenerated CFSGTwistedE6GeckRelativeWordTwist
open CFSGTwistedE6GeckPositiveTwist CFSGTwistedE6GeckDiagramCovariance
open CFSGTwistedE6GeckMatrixTwist CFSGTwistedE6GeckNormalizerEnvelope
open CFSGTwistedE6GeckInversionParts CFSGTwistedE6GeckSourceAction
open CFSGTwistedE6FixedWordClassification CFSGExceptionalNormTwoBases
open CFSGExceptionalCartanPositiveDefinite CFSGNormTwoGeckWeylWordDegree
open CFSGNormTwoGeckIntegralWord CFSGSubgroupConjugateOrbitCardinality
open CFSGFixedSubgroupConjugation CFSGSubgroupConjugateDisjoint
local notation "A" => CartanMatrix.E₆
local notation "hs" => CartanMatrix.E₆_transpose
local notation "hp" => E6_positive_definite

private theorem conjugate_cell {G : Type*} [Group G] (R : Subgroup G)
    (g u d W v : G) (he : g=(u*d)*W*v)
    (hv : v∈Subgroup.normalizer (R : Set G)) :
    R.map (MulAut.conj g).toMonoidHom=
      ((R.map (MulAut.conj W).toMonoidHom).map (MulAut.conj d).toMonoidHom).map
        (MulAut.conj u).toMonoidHom := by
  rw [he,conjugate_mul,conjugate_eq_of_mem_normalizer R v hv,conjugate_mul,conjugate_mul]

theorem fixed_opposite_conjugate_by_positive (K : Type) [Field K] [Finite K]
    (sigma : K≃+*K) (g : (Matrix GeckIndex GeckIndex K)ˣ)
    (hg : g∈MatrixGroup K) (hfixed : unitTwist K sigma g=g)
    (hdisj : signedFixed K sigma false⊓(signedFixed K sigma false).map
      (MulAut.conj g).toMonoidHom=⊥) :
    ∃u∈signedFixed K sigma false,(signedFixed K sigma false).map
      (MulAut.conj g).toMonoidHom=(signedFixed K sigma true).map
        (MulAut.conj u).toMonoidHom := by
  let R := signedFixed K sigma false
  let N := signedFixed K sigma true
  let tau := unitTwist K sigma
  have hz : (1 : MatrixGroup K)∈Subgroup.center (MatrixGroup K) := Subgroup.one_mem _
  have htwist : unitTwist K sigma g=(1 : MatrixGroup K).val*g := by simpa using hfixed
  obtain ⟨r,b,hb,v,he⟩ := exists_central_twisted_relative_cell K sigma g hg 1 hz htwist
  let W := wordUnit A hs hp E6Base E6Index K (expandRelative r)
  have hW : unitTwist K sigma W=W := by
    change unitTwist K sigma (wordUnit A hs hp E6Base E6Index K (expandRelative r))=
      wordUnit A hs hp E6Base E6Index K (expandRelative r)
    rw [word_eq_canonicalWord]
    exact relative_word_fixed K sigma r
  have hcell : unitTwist K sigma (b*W*inversionEmbedding K (expandRelative r) v)=
      (1 : MatrixGroup K).val*(b*W*inversionEmbedding K (expandRelative r) v) := by
    rw [←he]
    exact htwist
  have hcoords := central_twisted_cell_coordinates K sigma (expandRelative r) hW 1 hz
    ⟨b,hb⟩ v hcell
  obtain ⟨u,hu,huf,d,hd,hdf,hbe⟩ :=
    exists_central_twisted_envelope_factors K sigma b hb 1 hz hcoords.1
  have hdFixed : tau d=d := by simpa only [Subgroup.coe_one,one_mul] using hdf
  have huR : u∈R := ⟨hu,huf⟩
  have hvR : inversionEmbedding K (expandRelative r) v∈R := ⟨v.val.property,hcoords.2⟩
  have hdR : d∈Subgroup.normalizer (R : Set (Matrix GeckIndex GeckIndex K)ˣ) :=
    normalizes_inf_fixed tau (Positive K) d hdFixed hd.1.1
  have hdN : d∈Subgroup.normalizer (N : Set (Matrix GeckIndex GeckIndex K)ˣ) :=
    normalizes_inf_fixed tau (Negative K) d hdFixed hd.1.2
  have hmap : R.map (MulAut.conj g).toMonoidHom=
      ((R.map (MulAut.conj W).toMonoidHom).map (MulAut.conj d).toMonoidHom).map
        (MulAut.conj u).toMonoidHom := by
    apply conjugate_cell R g u d W _ _ (R.le_normalizer hvR)
    rw [he,hbe]
  have hstripU : R⊓(R.map (MulAut.conj W).toMonoidHom).map
      (MulAut.conj d).toMonoidHom=⊥ := by
    apply (inf_conjugate_eq_bot_iff R _ u (R.le_normalizer huR)).mp
    rw [←hmap]
    exact hdisj
  have hstripD : R⊓R.map (MulAut.conj W).toMonoidHom=⊥ :=
    (inf_conjugate_eq_bot_iff R _ d hdR).mp hstripU
  have hOpp : R.map (MulAut.conj W).toMonoidHom=N :=
    fixed_positive_image_eq_negative_of_disjoint K sigma r hstripD
  refine ⟨u,huR,?_⟩
  rw [hmap,hOpp,conjugate_eq_of_mem_normalizer N d hdN]

end SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckFixedBruhatOppositeAlignment
