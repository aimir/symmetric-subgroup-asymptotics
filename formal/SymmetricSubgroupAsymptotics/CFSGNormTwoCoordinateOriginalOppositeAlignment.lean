import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateElementaryOppositeAlignment
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateOriginalPositiveCenter
import SymmetricSubgroupAsymptotics.CFSGQuotientOppositeAlignment

/-! Opposite conjugates in the SAME original projective Serre model are
aligned by its actual projected Borel. Only group elements are lifted;
no arbitrary automorphism lift is asserted. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateOriginalOppositeAlignment
open CFSG.Models.Chevalley CFSGIntegerMatrixPairing CFSGNormTwoRootPairing
open CFSGGeckSerreRepresentation
open CFSGNormTwoGeckIntegralRealization CFSGNormTwoGeckPositivePGroup
open CFSGNormTwoCoordinateElementaryRootParameters CFSGNormTwoGeckBorelEnvelope
open CFSGNormTwoCoordinateElementaryOppositeAlignment
open CFSGNormTwoCoordinateOriginalPositiveCenter CFSGNormTwoCoordinateOriginalProjection
open CFSGNormTwoCoordinatePositiveQuotientInjectivity CFSGNormTwoCoordinateRootHeightQuotient
open CFSGQuotientOppositeAlignment
variable {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ) (hd : ∀j,A j j=2)
    (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    (ho : ∀i j,i≠j→A i j≤0)
    [Fintype (Roots A)] [DecidableEq (Roots A)]
    [(rootPairing A hs hp).IsReduced] [(rootPairing A hs hp).IsIrreducible]
    (K : Type) [Field K]
local notation "b₀" => coordinateBase A hd hs hp ho
local notation "s₀" => coordinateIndexEquiv A hd hs hp ho

def originalNegative [IsSimpleGroup (Projective (cartan b₀ s₀) K)] (i : Fin r) :
    Subgroup (Projective (cartan b₀ s₀) K) :=
  ((rootGroup A hs hp b₀ s₀ K true).subgroupOf (ElementaryGroup A hd hs hp ho K)).map
    (originalProjection A hd hs hp ho K i)

def originalBorel [IsSimpleGroup (Projective (cartan b₀ s₀) K)] (i : Fin r) :
    Subgroup (Projective (cartan b₀ s₀) K) :=
  ((borelEnvelope A hs hp b₀ s₀ K).subgroupOf (ElementaryGroup A hd hs hp ho K)).map
    (originalProjection A hd hs hp ho K i)

theorem originalPositive_eq_map [IsSimpleGroup (Projective (cartan b₀ s₀) K)] (i : Fin r) :
    originalPositive A hd hs hp ho K i=
      ((rootGroup A hs hp b₀ s₀ K false).subgroupOf (ElementaryGroup A hd hs hp ho K)).map
        (originalProjection A hd hs hp ho K i) := by
  rw [originalPositive,MonoidHom.range_comp,positiveInclusion,Subgroup.inclusion_range]

theorem originalBorel_le_normalizer_positive
    [IsSimpleGroup (Projective (cartan b₀ s₀) K)] (i : Fin r) :
    originalBorel A hd hs hp ho K i≤
      Subgroup.normalizer (originalPositive A hd hs hp ho K i : Set _) := by
  let H := ElementaryGroup A hd hs hp ho K
  let U := (rootGroup A hs hp b₀ s₀ K false).subgroupOf H
  let f := originalProjection A hd hs hp ho K i
  rw [originalPositive_eq_map A hd hs hp ho K i]
  rintro _ ⟨b,hb,rfl⟩
  apply Subgroup.le_normalizer_map f
  refine ⟨b,?_,rfl⟩
  apply Subgroup.mem_normalizer_iff.mpr
  intro x
  exact Subgroup.mem_normalizer_iff.mp
    (CFSGNormTwoGeckBorelNormalization.borelEnvelope_le_normalizer_positive
      A hs hp b₀ s₀ K hb) x.val

theorem original_opposite_conjugate_by_borel [Finite K] [Nontrivial (Fin r)]
    (p : ℕ) [Fact p.Prime] [CharP K p]
    [IsSimpleGroup (Projective (cartan b₀ s₀) K)] (i : Fin r)
    (g : Projective (cartan b₀ s₀) K)
    (hdisj : originalPositive A hd hs hp ho K i ⊓
      (originalPositive A hd hs hp ho K i).map (MulAut.conj g).toMonoidHom=⊥) :
    ∃b∈originalBorel A hd hs hp ho K i,
      (originalPositive A hd hs hp ho K i).map (MulAut.conj g).toMonoidHom=
        (originalNegative A hd hs hp ho K i).map (MulAut.conj b).toMonoidHom := by
  let H := ElementaryGroup A hd hs hp ho K
  let U := (rootGroup A hs hp b₀ s₀ K false).subgroupOf H
  let V := (rootGroup A hs hp b₀ s₀ K true).subgroupOf H
  let B := (borelEnvelope A hs hp b₀ s₀ K).subgroupOf H
  let f := originalProjection A hd hs hp ho K i
  have hU : Function.Injective (f.comp U.subtype) := by
    intro x y he
    have hh := originalProjection_positive_injective A hd hs hp ho K p i
      (a₁ := ⟨x.val.val,x.property⟩) (a₂ := ⟨y.val.val,y.property⟩) he
    have hval : x.val.val=y.val.val :=
      congrArg (fun z : PositiveGroup A hd hs hp ho K=>z.val) hh
    exact Subtype.ext (Subtype.ext hval)
  rw [originalPositive_eq_map A hd hs hp ho K i] at hdisj ⊢
  exact opposite_alignment_map f (originalProjection_surjective A hd hs hp ho K i)
    U V B hU (elementary_opposite_conjugate_by_borel A hd hs hp ho K) g hdisj

end SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateOriginalOppositeAlignment
