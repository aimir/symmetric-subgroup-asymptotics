import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateOriginalOppositionAut
import SymmetricSubgroupAsymptotics.CFSGPairSwappingAutomorphism

/-! Given an actual original automorphism preserving V, conjugation by
the fixed original opposition gives an actual U-preserving automorphism.
No automorphism lift or chosen matrix representative is involved. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateOriginalOppositionConjugation
open CFSG.Models.Chevalley CFSGIntegerMatrixPairing CFSGNormTwoRootPairing
open CFSGGeckSerreRepresentation CFSGNormTwoGeckIntegralRealization
open CFSGNormTwoGeckPositivePGroup CFSGNormTwoGeckFieldOpposition
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

open CFSGNormTwoCoordinateOriginalOppositionAut

def oppositionConjugate [IsSimpleGroup (Projective (cartan b₀ s₀) K)]
    (i : Fin r) (f : MulAut (Projective (cartan b₀ s₀) K)) :
    MulAut (Projective (cartan b₀ s₀) K) :=
  (originalOppositionAut A hd hs hp ho K i).symm*f*originalOppositionAut A hd hs hp ho K i

theorem oppositionConjugate_preserves_positive
    [IsSimpleGroup (Projective (cartan b₀ s₀) K)]
    (i : Fin r) (f : MulAut (Projective (cartan b₀ s₀) K))
    (hf : (originalNegative A hd hs hp ho K i).map f.toMonoidHom=
      originalNegative A hd hs hp ho K i) :
    (originalPositive A hd hs hp ho K i).map
      (oppositionConjugate A hd hs hp ho K i f).toMonoidHom=originalPositive A hd hs hp ho K i :=
  CFSGPairSwappingAutomorphism.conjugate_preserves_first
    (originalPositive A hd hs hp ho K i) (originalNegative A hd hs hp ho K i)
    (originalOppositionAut A hd hs hp ho K i) f
    (originalOpposition_positive A hd hs hp ho K i) hf

end SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateOriginalOppositionConjugation
