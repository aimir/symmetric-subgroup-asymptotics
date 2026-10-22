import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD4StarCliqueEquivalence
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD4PointTypeStabilizer

/-! The ACTUAL index-three point-type stabilizer acts on original
star sets and their proved injective geometric labels, preserving the
intrinsic two-common-plane relation. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD4ResidualSpace
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDIndexPlaneFamilyAction
variable (K : Type) [Field K] [Finite K] (p : ℕ) [Fact p.Prime] [CharP K p]

theorem pointType_non_top_image (f : naturalPointTypeStabilizer K p) (T : NonTopMaximalCliques K) :
    naturalCliqueType K (automorphismCliqueImage K p f.val T.val) ≠ 0 := by
  obtain ⟨P, hP⟩ := maximal_original_clique_nonempty K T.val T.property.1
  have hh := global_clique_type_formula K p f.val P T.val T.property.1 hP
  have hf0 : globalTypePermutation K p f.val 0 = 0 := f.property
  intro hz
  have he : globalTypePermutation K p f.val (naturalCliqueType K T.val) =
      globalTypePermutation K p f.val 0 := (hh.symm.trans hz).trans hf0.symm
  exact T.property.2 ((globalTypePermutation K p f.val).injective he)

def nonTopCliquePermutation (f : naturalPointTypeStabilizer K p) : Equiv.Perm (NonTopMaximalCliques K) where
  toFun T := ⟨automorphismCliqueImage K p f.val T.val,
    automorphismCliqueImage_maximal K p f.val T.val T.property.1, pointType_non_top_image K p f T⟩
  invFun T := ⟨automorphismCliqueImage K p (f⁻¹).val T.val,
    automorphismCliqueImage_maximal K p (f⁻¹).val T.val T.property.1, pointType_non_top_image K p f⁻¹ T⟩
  left_inv T := Subtype.ext (automorphismCliqueImage_inv_cancel K p f.val T.val)
  right_inv T := Subtype.ext (by simpa only [inv_inv] using automorphismCliqueImage_inv_cancel K p (f⁻¹).val T.val)

def nonTopCliqueAction : naturalPointTypeStabilizer K p →* Equiv.Perm (NonTopMaximalCliques K) where
  toFun := nonTopCliquePermutation K p
  map_one' := by
    apply Equiv.ext
    intro T
    exact Subtype.ext (automorphismCliqueImage_one K p T.val)
  map_mul' f g := by
    apply Equiv.ext
    intro T
    exact Subtype.ext (automorphismCliqueImage_mul K p f.val g.val T.val)

def starLabelAction : naturalPointTypeStabilizer K p →* Equiv.Perm (PointStarLabels K) :=
  ((starCliqueEquiv K).symm.permCongrHom.toMonoidHom).comp (nonTopCliqueAction K p)

theorem starLabelAction_sets (f : naturalPointTypeStabilizer K p) (S : PointStarLabels K) :
    pointStarPlanes K (starLabelAction K p f S) = automorphismCliqueImage K p f.val (pointStarPlanes K S) := by
  let T := nonTopCliqueAction K p f (starCliqueEquiv K S)
  have hh := (starCliqueEquiv K).apply_symm_apply T
  exact congrArg Subtype.val hh

theorem starLabelAction_shared_pair (f : naturalPointTypeStabilizer K p) (S T : PointStarLabels K)
    (h : SharedStarPair K S T) : SharedStarPair K (starLabelAction K p f S) (starLabelAction K p f T) := by
  obtain ⟨P, Q, hne, hP, hQ⟩ := h
  let e := singularActionHom K p 0 f.val
  refine ⟨e P, e Q, (fun he => hne (e.injective he)), ?_, ?_⟩
  · constructor
    · rw [starLabelAction_sets]
      exact ⟨P, hP.1, rfl⟩
    · rw [starLabelAction_sets]
      exact ⟨P, hP.2, rfl⟩
  · constructor
    · rw [starLabelAction_sets]
      exact ⟨Q, hQ.1, rfl⟩
    · rw [starLabelAction_sets]
      exact ⟨Q, hQ.2, rfl⟩

theorem starLabelAction_shared_path (f : naturalPointTypeStabilizer K p) (S T : PointStarLabels K)
    (h : Relation.ReflTransGen (SharedStarPair K) S T) :
    Relation.ReflTransGen (SharedStarPair K) (starLabelAction K p f S) (starLabelAction K p f T) :=
  Relation.ReflTransGen.lift (starLabelAction K p f) (fun _ _ => starLabelAction_shared_pair K p f _ _) h

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD4ResidualSpace
