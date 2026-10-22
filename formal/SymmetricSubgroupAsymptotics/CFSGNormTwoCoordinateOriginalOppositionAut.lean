import SymmetricSubgroupAsymptotics.CFSGCentralKernelAutomorphismDescent
import SymmetricSubgroupAsymptotics.CFSGInvariantSubgroupCoordinateImage
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateOppositeNormalizerIntersection
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateOriginalCentralKernel
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateOriginalOppositeAlignment

/-! The GIVEN canonical opposition normalizes the actual elementary
group and therefore descends to an involutive automorphism of the SAME
original projective Serre model. It exchanges its literal U and V.
There is no lifting claim for arbitrary original automorphisms. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateOriginalOppositionAut
open CFSG.Models.Chevalley CFSGIntegerMatrixPairing CFSGNormTwoRootPairing
open CFSGGeckSerreRepresentation CFSGNormTwoGeckIntegralRealization
open CFSGNormTwoGeckPositivePGroup CFSGNormTwoGeckFieldOpposition
open CFSGNormTwoGeckOppositionDegree
open CFSGNormTwoGeckOppositeIntersection CFSGNormTwoCoordinateOppositeNormalizerIntersection
open CFSGNormTwoCoordinateRootHeightQuotient CFSGNormTwoCoordinatePositiveQuotientInjectivity
open CFSGNormTwoCoordinateElementaryRootParameters
open CFSGNormTwoCoordinateOriginalProjection CFSGNormTwoCoordinateOriginalCentralKernel
open CFSGNormTwoCoordinateOriginalPositiveCenter CFSGNormTwoCoordinateOriginalOppositeAlignment
open CFSGInvariantSubgroupCoordinateImage CFSGCentralKernelAutomorphismDescent
variable {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ) (hd : ∀j,A j j=2)
    (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    (ho : ∀i j,i≠j→A i j≤0)
    [Fintype (Roots A)] [DecidableEq (Roots A)]
    [(rootPairing A hs hp).IsReduced] [(rootPairing A hs hp).IsIrreducible]
    (K : Type) [Field K] [Nontrivial (Fin r)]
local notation "b₀" => coordinateBase A hd hs hp ho
local notation "s₀" => coordinateIndexEquiv A hd hs hp ho
local notation "H" => ElementaryGroup A hd hs hp ho K
local notation "U" => rootGroup A hs hp b₀ s₀ K false
local notation "V" => rootGroup A hs hp b₀ s₀ K true

def elementaryOppositionAut : MulAut H :=
  restrictAut H (MulAut.conj (oppositionUnit A hs hp b₀ K))
    (opposition_elementary_eq_elementary A hd hs hp ho K)

theorem elementaryOpposition_positive :
    ((U).subgroupOf H).map (elementaryOppositionAut A hd hs hp ho K).toMonoidHom=
      (V).subgroupOf H := by
  have hjoin : U⊔V=H := positive_sup_negative A hs hp b₀ s₀ K
  have hUH : U≤H := by rw [←hjoin];exact le_sup_left
  have hVH : V≤H := by rw [←hjoin];exact le_sup_right
  exact restrictAut_map H U V (MulAut.conj (oppositionUnit A hs hp b₀ K))
    (opposition_elementary_eq_elementary A hd hs hp ho K) hUH hVH
    (opposition_positive_eq_negative A hs hp b₀ s₀ K)

theorem elementaryOpposition_negative :
    ((V).subgroupOf H).map (elementaryOppositionAut A hd hs hp ho K).toMonoidHom=
      (U).subgroupOf H := by
  have hjoin : U⊔V=H := positive_sup_negative A hs hp b₀ s₀ K
  have hUH : U≤H := by rw [←hjoin];exact le_sup_left
  have hVH : V≤H := by rw [←hjoin];exact le_sup_right
  exact restrictAut_map H V U (MulAut.conj (oppositionUnit A hs hp b₀ K))
    (opposition_elementary_eq_elementary A hd hs hp ho K) hVH hUH
    (opposition_negative_eq_positive A hd hs hp ho K)

def originalOppositionAut [IsSimpleGroup (Projective (cartan b₀ s₀) K)] (i : Fin r) :
    MulAut (Projective (cartan b₀ s₀) K) :=
  descend (originalProjection A hd hs hp ho K i)
    (originalProjection_surjective A hd hs hp ho K i)
    (originalProjection_kernel_eq_center A hd hs hp ho K i)
    (elementaryOppositionAut A hd hs hp ho K)

theorem originalOppositionAut_apply [IsSimpleGroup (Projective (cartan b₀ s₀) K)]
    (i : Fin r) (x : H) :
    originalOppositionAut A hd hs hp ho K i (originalProjection A hd hs hp ho K i x)=
      originalProjection A hd hs hp ho K i (elementaryOppositionAut A hd hs hp ho K x) :=
  descend_apply _ _ _ _ x

theorem originalOpposition_positive [IsSimpleGroup (Projective (cartan b₀ s₀) K)] (i : Fin r) :
    (originalPositive A hd hs hp ho K i).map (originalOppositionAut A hd hs hp ho K i).toMonoidHom=
      originalNegative A hd hs hp ho K i := by
  rw [originalPositive_eq_map]
  change (((U).subgroupOf H).map (originalProjection A hd hs hp ho K i)).map
    (descend _ _ _ (elementaryOppositionAut A hd hs hp ho K)).toMonoidHom=_
  rw [descend_subgroup_image,elementaryOpposition_positive]
  rfl

theorem originalOpposition_negative [IsSimpleGroup (Projective (cartan b₀ s₀) K)] (i : Fin r) :
    (originalNegative A hd hs hp ho K i).map (originalOppositionAut A hd hs hp ho K i).toMonoidHom=
      originalPositive A hd hs hp ho K i := by
  rw [originalPositive_eq_map]
  change (((V).subgroupOf H).map (originalProjection A hd hs hp ho K i)).map
    (descend _ _ _ (elementaryOppositionAut A hd hs hp ho K)).toMonoidHom=_
  rw [descend_subgroup_image,elementaryOpposition_negative]

theorem originalOpposition_involutive [IsSimpleGroup (Projective (cartan b₀ s₀) K)] (i : Fin r) :
    Function.Involutive (originalOppositionAut A hd hs hp ho K i) := by
  intro x
  obtain ⟨y,rfl⟩ := originalProjection_surjective A hd hs hp ho K i x
  rw [originalOppositionAut_apply,originalOppositionAut_apply]
  congr 1
  apply Subtype.ext
  exact opposition_twice A hs hp b₀ K y.val

end SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateOriginalOppositionAut
