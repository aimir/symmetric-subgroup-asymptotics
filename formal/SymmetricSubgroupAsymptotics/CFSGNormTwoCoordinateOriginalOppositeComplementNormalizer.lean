import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateOriginalComplementNormalizer
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateOriginalOppositeComplementAction

/-! The FULL normalizer of the actual original opposite complement is
N(V) extended by the actual positive simple-root subgroup. This is an
identity of literal subgroups, with all quotient and opposition maps
proved, rather than a new parabolic recognition premise. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateOriginalOppositeComplementNormalizer
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

open CFSGNormTwoCoordinateOriginalComplementNormalizer CFSGNormTwoCoordinateOriginalOppositionAut
open CFSGNormTwoCoordinateOriginalOppositeComplementAction CFSGNormTwoGeckFieldOpposition
open CFSGNormTwoCoordinateOppositeNormalizerIntersection CFSGInvariantSubgroupCoordinateImage
open CFSGCentralKernelAutomorphismDescent

theorem elementaryOpposition_negative_simple (j : Fin r) :
    ((canonicalRootSubgroup D K true j).subgroupOf (ElementaryGroup A hd hs hp ho K)).map
      (elementaryOppositionAut A hd hs hp ho K).toMonoidHom=
      (canonicalRootSubgroup D K false j).subgroupOf (ElementaryGroup A hd hs hp ho K) := by
  have hn : canonicalRootSubgroup D K true j≤ElementaryGroup A hd hs hp ho K := by
    rintro g ⟨a,rfl⟩
    exact (canonicalElementaryRoot D K true j a).property
  have hp' : canonicalRootSubgroup D K false j≤ElementaryGroup A hd hs hp ho K := by
    rintro g ⟨a,rfl⟩
    exact (canonicalElementaryRoot D K false j a).property
  have he : (canonicalRootSubgroup D K true j).map
      (MulAut.conj (oppositionUnit A hs hp b₀ K)).toMonoidHom=canonicalRootSubgroup D K false j := by
    apply Subgroup.ext
    intro x
    constructor
    · rintro ⟨y,⟨a,rfl⟩,rfl⟩
      exact ⟨a,(canonicalRoot_conjugate A hs hp b₀ s₀ K true j a).symm⟩
    · rintro ⟨a,rfl⟩
      exact ⟨canonicalRoot D K true j a,⟨a,rfl⟩,
        canonicalRoot_conjugate A hs hp b₀ s₀ K true j a⟩
  exact restrictAut_map (ElementaryGroup A hd hs hp ho K)
    (canonicalRootSubgroup D K true j) (canonicalRootSubgroup D K false j)
    (MulAut.conj (oppositionUnit A hs hp b₀ K))
    (opposition_elementary_eq_elementary A hd hs hp ho K) hn hp' he

theorem originalOpposition_negative_simple
    [IsSimpleGroup (Projective (cartan b₀ s₀) K)] (i j : Fin r) :
    (originalNegativeSimpleRootGroup A hd hs hp ho K i j).map
      (originalOppositionAut A hd hs hp ho K i).toMonoidHom=
        originalSimpleRootGroup A hd hs hp ho K i j := by
  change (((canonicalRootSubgroup D K true j).subgroupOf (ElementaryGroup A hd hs hp ho K)).map
    (originalProjection A hd hs hp ho K i)).map
      (descend _ _ _ (elementaryOppositionAut A hd hs hp ho K)).toMonoidHom=
        ((canonicalRootSubgroup D K false j).subgroupOf (ElementaryGroup A hd hs hp ho K)).map
          (originalProjection A hd hs hp ho K i)
  rw [descend_subgroup_image,elementaryOpposition_negative_simple]

theorem original_opposite_complement_normalizer
    (ε : Fin r→ℤ) (hε : ∀j,ε j*ε j=1) (hA : ∀i j,ε i*|A i j|=A j i*ε j)
    (hidentity : ∀w : List (Fin r),wordUnit A hs hp b₀ s₀ K w∈
      Subgroup.normalizer (rootGroup A hs hp b₀ s₀ K false : Set _)→wordLinear A hs hp b₀ s₀ w=1)
    (p : ℕ) [Fact p.Prime] [CharP K p]
    [IsSimpleGroup (Projective (cartan b₀ s₀) K)] (i j : Fin r) :
    Subgroup.normalizer (originalOppositeComplement A hd hs hp ho K p i j : Set _)=
      Subgroup.normalizer (originalNegative A hd hs hp ho K i : Set _)⊔
        originalSimpleRootGroup A hd hs hp ho K i j := by
  have hh := congrArg
    (fun S : Subgroup (Projective (cartan b₀ s₀) K)=>S.map
      (originalOppositionAut A hd hs hp ho K i).toMonoidHom)
    (original_complement_normalizer A hd hs hp ho K ε hε hA hidentity p i j)
  dsimp only at hh
  simp only [Subgroup.map_sup,Subgroup.map_equiv_normalizer_eq,
    originalOpposition_positive A hd hs hp ho K i,
    originalOpposition_negative_simple A hd hs hp ho K i j] at hh
  exact hh

end SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateOriginalOppositeComplementNormalizer
