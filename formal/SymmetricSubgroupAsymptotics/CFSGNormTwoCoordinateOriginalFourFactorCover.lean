import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateBruhatCover
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateOriginalProjection
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinatePositiveCardinality
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckTorusCardinality

/-! A four-factor cover of the actual original projective model by its
positive image, genuine torus image, literal Weyl-word image, and positive
image.  Only elements are lifted through the proved original projection.
The two torus factors in the Bruhat cover are combined using the actual
normalization identities. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateOriginalFourFactorCover
open CFSG.Models.Chevalley CFSGIntegerMatrixPairing CFSGNormTwoRootPairing
open CFSGGeckSerreRepresentation
open CFSGNormTwoGeckIntegralRealization CFSGNormTwoGeckWeylWordDegree
open CFSGNormTwoGeckBorelEnvelope CFSGNormTwoGeckBorelFactorization
open CFSGNormTwoGeckBorelNormalization CFSGNormTwoGeckWeylWordTorus
open CFSGNormTwoCoordinateBruhatCover CFSGNormTwoCoordinateElementaryRootParameters
open CFSGNormTwoCoordinateOriginalProjection CFSGNormTwoCoordinatePositiveRootGenerators
open CFSGNormTwoCoordinatePositiveCardinality CFSGNormTwoGeckTorusCardinality
open CFSGNormTwoCoordinateRootHeightQuotient
variable {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ) (hd : ∀j,A j j=2)
    (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    (ho : ∀i j,i≠j→A i j≤0)
    [Fintype (Roots A)] [DecidableEq (Roots A)]
    [(rootPairing A hs hp).IsReduced] [(rootPairing A hs hp).IsIrreducible]
    (K : Type) [Field K]
local notation "b₀" => coordinateBase A hd hs hp ho
local notation "s₀" => coordinateIndexEquiv A hd hs hp ho

theorem exists_canonical_four_factor (g : ElementaryGroup A hd hs hp ho K) :
    ∃u∈PositiveGroup A hd hs hp ho K,
      ∃t∈torusGroup A hs hp b₀ s₀ K,∃w:List (Fin r),
        ∃v∈PositiveGroup A hd hs hp ho K,
          g.val=u*t*wordUnit A hs hp b₀ s₀ K w*v := by
  obtain ⟨w,b,hb,c,hc,hg⟩:=canonical_bruhat_cover A hd hs hp ho K g.val g.property
  obtain ⟨u,hu,t,ht,hb⟩:=borel_factor A hs hp b₀ s₀ K b hb
  obtain ⟨v,hv,s,hsT,hc⟩:=borel_factor A hs hp b₀ s₀ K c hc
  let U:=PositiveGroup A hd hs hp ho K
  let T:=torusGroup A hs hp b₀ s₀ K
  let W:=wordUnit A hs hp b₀ s₀ K w
  have hsN : s∈Subgroup.normalizer (U:Set _) :=
    (le_trans (show T≤borelEnvelope A hs hp b₀ s₀ K from le_sup_right)
      (borelEnvelope_le_normalizer_positive A hs hp b₀ s₀ K)) hsT
  have hv' : s⁻¹*v*s∈U := by
    exact (Subgroup.mem_set_normalizer_iff''.mp hsN v).mp hv
  have ht' : W*s*W⁻¹∈T :=
    (Subgroup.mem_normalizer_iff.mp (wordUnit_mem_torus_normalizer A hs hp b₀ s₀ K w) s).mp hsT
  refine ⟨u,hu,t*(W*s*W⁻¹),T.mul_mem ht ht',w,s⁻¹*v*s,hv',?_⟩
  rw [hg,hb,hc]
  change (u*t)*W*(v*s)=u*(t*(W*s*W⁻¹))*W*(s⁻¹*v*s)
  group

def torusInclusion : torusGroup A hs hp b₀ s₀ K→*ElementaryGroup A hd hs hp ho K :=
  (torusGroup A hs hp b₀ s₀ K).subtype.codRestrict _
    (fun t=>torusGroup_le_canonical A hs hp b₀ s₀ K t.property)

def positiveProjection [IsSimpleGroup (Projective (cartan b₀ s₀) K)] (i:Fin r) :=
  (originalProjection A hd hs hp ho K i).comp
    (CFSGNormTwoCoordinatePositiveQuotientInjectivity.positiveInclusion A hd hs hp ho K)

def torusProjection [IsSimpleGroup (Projective (cartan b₀ s₀) K)] (i:Fin r) :=
  (originalProjection A hd hs hp ho K i).comp (torusInclusion A hd hs hp ho K)

theorem exists_original_four_factor
    [IsSimpleGroup (Projective (cartan b₀ s₀) K)] (i:Fin r)
    (g:Projective (cartan b₀ s₀) K) :
    ∃u:(positiveProjection A hd hs hp ho K i).range,
      ∃t:(torusProjection A hd hs hp ho K i).range,
        ∃w:{y // y∈Set.range (fun v:List (Fin r)=>
          originalProjection A hd hs hp ho K i (elementaryWord A hd hs hp ho K v))},
          ∃v:(positiveProjection A hd hs hp ho K i).range,
            g=u.val*t.val*w.val*v.val := by
  obtain ⟨x,rfl⟩:=originalProjection_surjective A hd hs hp ho K i g
  obtain ⟨u,hu,t,ht,w,v,hv,he⟩:=exists_canonical_four_factor A hd hs hp ho K x
  let U:PositiveGroup A hd hs hp ho K:=⟨u,hu⟩
  let T:torusGroup A hs hp b₀ s₀ K:=⟨t,ht⟩
  let V:PositiveGroup A hd hs hp ho K:=⟨v,hv⟩
  refine ⟨⟨_,⟨U,rfl⟩⟩,⟨_,⟨T,rfl⟩⟩,
    ⟨_,⟨w,rfl⟩⟩,⟨_,⟨V,rfl⟩⟩,?_⟩
  have hx : x=
      CFSGNormTwoCoordinatePositiveQuotientInjectivity.positiveInclusion A hd hs hp ho K U*
      torusInclusion A hd hs hp ho K T*elementaryWord A hd hs hp ho K w*
      CFSGNormTwoCoordinatePositiveQuotientInjectivity.positiveInclusion A hd hs hp ho K V :=
    Subtype.ext he
  exact congrArg (originalProjection A hd hs hp ho K i) hx |>.trans (by
    simp only [map_mul]; rfl)

theorem positiveProjection_card_le [Finite K]
    [IsSimpleGroup (Projective (cartan b₀ s₀) K)] (i:Fin r) :
    Nat.card (positiveProjection A hd hs hp ho K i).range≤
      Nat.card K^Nat.card (PositiveRoot A) := by
  have h:=Nat.card_le_card_of_surjective (positiveProjection A hd hs hp ho K i).rangeRestrict
    (positiveProjection A hd hs hp ho K i).rangeRestrict_surjective
  exact h.trans_eq (positive_card A hd hs hp ho K)

omit [(rootPairing A hs hp).IsReduced] in
theorem torusProjection_card_le [Finite K]
    [IsSimpleGroup (Projective (cartan b₀ s₀) K)] (i:Fin r) :
    Nat.card (torusProjection A hd hs hp ho K i).range≤Nat.card K^r := by
  have h:=Nat.card_le_card_of_surjective (torusProjection A hd hs hp ho K i).rangeRestrict
    (torusProjection A hd hs hp ho K i).rangeRestrict_surjective
  exact h.trans (torus_card_le_field_pow A hs hp b₀ s₀ K)

end SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateOriginalFourFactorCover
