import SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckCentralTwistedCellFactors
import SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckRelativeWordTwist
import SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckRelativeRootGenerated

/-! The actual positive/inversion decomposition of a fixed positive E6
element has fixed factors. This is a consequence of unique enlarged-
envelope/inversion coordinates, not exactness of a fixed-point functor.
The coefficient automorphism is arbitrary. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGE6GeckFixedPositiveInversionFactors
open CFSGTwistedE6GeckDiagramCovariance CFSGTwistedE6GeckSourceAction
open CFSGTwistedE6GeckPositiveTwist CFSGTwistedE6GeckMatrixTwist
open CFSGTwistedE6GeckRelativeRootGenerated CFSGTwistedE6GeckRelativeWordTwist
open CFSGTwistedE6GeckNormalizerEnvelope CFSGTwistedE6GeckInversionParts
open CFSGTwistedE6GeckCentralTwistedCellFactors CFSGTwistedE6FixedWordClassification
open CFSGNormTwoGeckWeylWordDegree CFSGNormTwoGeckIntegralWord
open CFSGExceptionalNormTwoBases CFSGExceptionalCartanPositiveDefinite
local notation "A" => CartanMatrix.E₆
local notation "hs" => CartanMatrix.E₆_transpose
local notation "hp" => E6_positive_definite

private theorem first_factor_fixed {G : Type*} [Group G] (T : G→*G)
    (u p v : G) (he : u=p*v) (hu : T u=u) (hv : T v=v) : T p=p := by
  have h := congrArg T he
  rw [map_mul,hu,hv] at h
  exact mul_right_cancel (h.symm.trans he)

theorem exists_fixed_positive_inversion_factors (K : Type) [Field K] [Finite K]
    (sigma : K≃+*K) (r : List (Fin 4)) (u : Positive K)
    (hu : unitTwist K sigma u.val=u.val) :
    ∃p∈CFSGTwistedE6GeckRelativeRootGenerated.signedFixed K sigma false,
      ∃v : InversionPart K (expandRelative r),
      inversionEmbedding K (expandRelative r) v∈
        CFSGTwistedE6GeckRelativeRootGenerated.signedFixed K sigma false ∧
      u.val=p*inversionEmbedding K (expandRelative r) v ∧
      wordUnit A hs hp E6Base E6Index K (expandRelative r)*p*
        (wordUnit A hs hp E6Base E6Index K (expandRelative r))⁻¹∈Positive K := by
  let W := wordUnit A hs hp E6Base E6Index K (expandRelative r)
  have hW : unitTwist K sigma W=W := by
    simpa only [W,word_eq_canonicalWord] using
      CFSGTwistedE6GeckRelativeWordTwist.relative_word_fixed K sigma r
  obtain ⟨p,hpW,v,hprod⟩ := exists_positive_inversion_factors K (expandRelative r) u
  let b : envelopePart K := ⟨W*p*W⁻¹,positive_le_envelope K hpW⟩
  have hcell : b.val*W*inversionEmbedding K (expandRelative r) v=W*u.val := by
    change (W*p*W⁻¹)*W*inversionEmbedding K (expandRelative r) v=W*u.val
    rw [hprod]
    group
  have htwist : unitTwist K sigma (b.val*W*inversionEmbedding K (expandRelative r) v)=
      (1 : MatrixGroup K).val*(b.val*W*inversionEmbedding K (expandRelative r) v) := by
    change unitTwist K sigma (b.val*W*inversionEmbedding K (expandRelative r) v)=
      1*(b.val*W*inversionEmbedding K (expandRelative r) v)
    rw [one_mul,hcell,map_mul,hW,hu]
  have hvfix := (central_twisted_cell_coordinates K sigma (expandRelative r) hW
    (1 : MatrixGroup K) (Subgroup.one_mem _) b v htwist).2
  have hpval : p=u.val*(inversionEmbedding K (expandRelative r) v)⁻¹ := by
    rw [hprod]
    group
  have hppos : p∈Positive K := by
    rw [hpval]
    exact (Positive K).mul_mem u.property ((Positive K).inv_mem v.val.property)
  have hpfix : unitTwist K sigma p=p := first_factor_fixed (unitTwist K sigma).toMonoidHom
    u.val p (inversionEmbedding K (expandRelative r) v) hprod hu hvfix
  exact ⟨p,⟨hppos,hpfix⟩,v,⟨v.val.property,hvfix⟩,hprod,hpW⟩

end SymmetricSubgroupAsymptotics.CFSGE6GeckFixedPositiveInversionFactors
