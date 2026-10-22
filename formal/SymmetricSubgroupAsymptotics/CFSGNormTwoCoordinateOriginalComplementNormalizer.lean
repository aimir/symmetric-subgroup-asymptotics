import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateElementaryComplementNormalizer
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateOriginalComplementAmbient
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateOriginalNormalizerIntersection

/-! The FULL original complement normalizer is its full positive
normalizer extended by the actual projected negative simple subgroup.
The normalizer-image equality uses proved central p-element separation. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateOriginalComplementNormalizer
open CFSG.Models.Chevalley CFSGIntegerMatrixPairing CFSGNormTwoRootPairing
open CFSGGeckSerreRepresentation CFSGNormTwoGeckIntegralRealization
open CFSGNormTwoCoordinateOriginalProjection CFSGNormTwoCoordinateOriginalCentralKernel
open CFSGNormTwoCoordinateElementaryRootParameters CFSGNormTwoCoordinatePositiveSylow
open CFSGNormTwoGeckWeylWordDegree CFSGNormTwoGeckWeylLatticeLinear
open CFSGNormTwoGeckPositivePGroup CFSGNormTwoCoordinatePositivePGroup CFSGSerreQuadraticMatrix
open CFSGNormTwoCoordinatePositiveQuotientInjectivity
open CFSGNormTwoCoordinateOriginalPositiveCenter CFSGNormTwoCoordinateOriginalOppositeAlignment
open CFSGNormTwoCoordinateElementaryNormalizerIntersection CFSGQuotientNormalizerIntersection
variable {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ) (hd : ∀j,A j j=2)
    (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    (ho : ∀i j,i≠j→A i j≤0)
    [Fintype (Roots A)] [DecidableEq (Roots A)]
    [(rootPairing A hs hp).IsReduced] [(rootPairing A hs hp).IsIrreducible]
    (K : Type) [Field K] [Finite K] [Nontrivial (Fin r)]
local notation "b₀" => coordinateBase A hd hs hp ho
local notation "s₀" => coordinateIndexEquiv A hd hs hp ho
local notation "D" => realizationData A hs hp b₀ s₀

open CFSGNormTwoGeckPositiveComplement CFSGNormTwoCoordinateElementaryComplementNormalizer
open CFSGNormTwoCoordinateOriginalComplementAmbient CFSGNormTwoCoordinateOriginalNormalizerIntersection

def originalNegativeSimpleRootGroup [IsSimpleGroup (Projective (cartan b₀ s₀) K)]
    (i j : Fin r) : Subgroup (Projective (cartan b₀ s₀) K) :=
  ((canonicalRootSubgroup D K true j).subgroupOf (ElementaryGroup A hd hs hp ho K)).map
    (originalProjection A hd hs hp ho K i)

theorem original_complement_normalizer
    (ε : Fin r→ℤ) (hε : ∀j,ε j*ε j=1) (hA : ∀i j,ε i*|A i j|=A j i*ε j)
    (hidentity : ∀w : List (Fin r),wordUnit A hs hp b₀ s₀ K w∈
      Subgroup.normalizer (rootGroup A hs hp b₀ s₀ K false : Set _)→wordLinear A hs hp b₀ s₀ w=1)
    (p : ℕ) [Fact p.Prime] [CharP K p]
    [IsSimpleGroup (Projective (cartan b₀ s₀) K)] (i j : Fin r) :
    Subgroup.normalizer (originalComplementAmbient A hd hs hp ho K p i j : Set _)=
      Subgroup.normalizer (originalPositive A hd hs hp ho K i : Set _)⊔
        originalNegativeSimpleRootGroup A hd hs hp ho K i j := by
  let H := ElementaryGroup A hd hs hp ho K
  let U := rootGroup A hs hp b₀ s₀ K false
  let M := positiveComplement A hs hp b₀ s₀ K j
  let UH := U.subgroupOf H
  let MH := M.subgroupOf H
  let f := originalProjection A hd hs hp ho K i
  have hjoin : U⊔rootGroup A hs hp b₀ s₀ K true=H := positive_sup_negative A hs hp b₀ s₀ K
  have hUH : U≤H := by rw [←hjoin];exact le_sup_left
  have hUp : IsPGroup p UH :=
    (rootGroup_isPGroup A hd hs hp ho s₀ K p false).of_injective
      (Subgroup.subgroupOfEquivOfLe hUH).toMonoidHom (Subgroup.subgroupOfEquivOfLe hUH).injective
  have hMUH : MH≤UH := by
    intro x hx
    exact CFSGNormTwoGeckPositiveComplement.complement_le_positive A hs hp b₀ s₀ K j hx
  have hMp : IsPGroup p MH := hUp.of_injective
    (Subgroup.inclusion hMUH) (Subgroup.inclusion_injective hMUH)
  have hh := congrArg (fun S : Subgroup H=>S.map f)
    (elementary_complement_normalizer A hd hs hp ho K ε hε hA hidentity j)
  dsimp only at hh
  rw [Subgroup.map_sup,
    originalProjection_normalizer_map A hd hs hp ho K ε hε hA hidentity p i MH hMp,
    originalProjection_normalizer_map A hd hs hp ho K ε hε hA hidentity p i UH hUp] at hh
  have hMproj : MH.map f=originalComplementAmbient A hd hs hp ho K p i j :=
    (originalComplementAmbient_eq_projection A hd hs hp ho K p i j).symm
  have hUproj : UH.map f=originalPositive A hd hs hp ho K i :=
    (originalPositive_eq_map A hd hs hp ho K i).symm
  rw [hMproj,hUproj] at hh
  exact hh

end SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateOriginalComplementNormalizer
