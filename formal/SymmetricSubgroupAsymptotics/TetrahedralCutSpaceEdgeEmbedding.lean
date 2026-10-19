import SymmetricSubgroupAsymptotics.TetrahedralCutSpaceRepresentation
import SymmetricSubgroupAsymptotics.RepresentationHeadExact
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.TetrahedralCutSpaceEdgeEmbedding
open AlternatingEdgeOriginalProjectorHeads (Top)
open TetrahedralCutSpaceCoinvariantHead (Bit Vector)

def coefficient (i : Fin 4) : Vector →ₗ[Bit] Bit :=
  ![0,LinearMap.proj 0,LinearMap.proj 1,LinearMap.proj 2] i

def linear : Vector →ₗ[Bit] AlternatingEdgeBinaryProjectors.Vector :=
  LinearMap.pi fun i => coefficient (SymmetricFourTwelvePointSocles.ends i).1+
    coefficient (SymmetricFourTwelvePointSocles.ends i).2

def embedding : Representation.IntertwiningMap
    TetrahedralCutSpaceRepresentation.beta AlternatingEdgeOriginalProjectorHeads.beta where
  toLinearMap := linear
  isIntertwining' p := by
    apply LinearMap.ext
    intro v
    funext i
    have h : ∀ (q : Equiv.Perm (Fin 4)) (w : Vector) (j : Fin 6),
        linear (TetrahedralCutSpaceRepresentation.rho q w) j=
          AlternatingEdgeBinaryProjectors.rho q (linear w) j := by decide +kernel
    exact h p.val v i

theorem embedding_injective : Function.Injective embedding := by
  have h : ∀ v w : Vector,linear v=linear w → v=w := by decide +kernel
  exact h

theorem basis_masks : ∀ i : Fin 3,linear (Pi.single i 1)=
    binaryVectorOfMask 6 (![25,42,52] i) := by decide +kernel

 def moduleEquiv {A : Rep.{0} Bit Top}
    (j : Representation.IntertwiningMap A.ρ AlternatingEdgeOriginalProjectorHeads.beta)
    (hj : Function.Injective j) (hr : j.range=embedding.range) :
    TetrahedralCutSpaceRepresentation.beta.Equiv A.ρ := by
  let eA : A.ρ.Equiv j.range.toRepresentation :=
    (RepresentationHeadExact.rangeProjection j).ofBijective
      ⟨fun _ _ h => hj (congrArg Subtype.val h),
        RepresentationHeadExact.rangeProjection_surjective j⟩
  let eR : TetrahedralCutSpaceRepresentation.beta.Equiv embedding.range.toRepresentation :=
    (RepresentationHeadExact.rangeProjection embedding).ofBijective
      ⟨fun _ _ h => embedding_injective (congrArg Subtype.val h),
        RepresentationHeadExact.rangeProjection_surjective embedding⟩
  have eR' : TetrahedralCutSpaceRepresentation.beta.Equiv j.range.toRepresentation := hr.symm ▸ eR
  exact eR'.trans eA.symm
end SymmetricSubgroupAsymptotics.TetrahedralCutSpaceEdgeEmbedding
