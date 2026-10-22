import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateGoodSylow
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateElementaryRootParameters

/-! Exposes the LITERAL positive subgroup as a Sylow, using the proved
normalizer p-maximality. The word-identity/sign premises have existing
exact E6/E7/E8 installers; no new model theorem is claimed by an alias. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinatePositiveSylow
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing
open CFSGNormTwoGeckIntegralRealization CFSGNormTwoGeckPositivePGroup
open CFSGNormTwoGeckWeylWordDegree CFSGNormTwoGeckWeylLatticeLinear
open CFSGNormTwoCoordinateNormalizerDiagonalFactor CFSGNormTwoCoordinateHeight
open CFSGNormTwoCoordinateElementaryRootParameters
variable {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ) (hd : ∀i,A i i=2)
    (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    (ho : ∀i j,i≠j→A i j≤0)
    [Fintype (Roots A)] [DecidableEq (Roots A)]
    [(rootPairing A hs hp).IsReduced] [(rootPairing A hs hp).IsIrreducible]
local notation "b₀" => coordinateBase A hd hs hp ho
local notation "s₀" => coordinateIndexEquiv A hd hs hp ho

def canonicalPositiveSylow (K : Type) [Field K] [Finite K]
    (ε : Fin r→ℤ) (hε : ∀i,ε i*ε i=1) (hA : ∀i j,ε i*|A i j|=A j i*ε j)
    (hidentity : ∀w : List (Fin r),wordUnit A hs hp b₀ s₀ K w∈
      Subgroup.normalizer (rootGroup A hs hp b₀ s₀ K false : Set _)→wordLinear A hs hp b₀ s₀ w=1)
    (p : ℕ) [Fact p.Prime] [CharP K p] : Sylow p (ElementaryGroup A hd hs hp ho K) := by
  letI : Fintype K := Fintype.ofFinite K
  let H := ElementaryGroup A hd hs hp ho K
  let U := rootGroup A hs hp b₀ s₀ K false
  have hUH : U≤H := by
    change U≤CFSGSerreQuadraticMatrix.canonicalElementaryGroup (realizationData A hs hp b₀ s₀) K
    rw [←positive_sup_negative A hs hp b₀ s₀ K]
    exact le_sup_left
  let UH := U.subgroupOf H
  have hUp : IsPGroup p UH :=
    (positive_isPGroup A hs hp b₀ s₀ coordinateHeight (simple_height A hd hs hp ho) K p).of_injective
      (Subgroup.subgroupOfEquivOfLe hUH).toMonoidHom (Subgroup.subgroupOfEquivOfLe hUH).injective
  have hm : UH.map H.subtype=U := by
    rw [Subgroup.subgroupOf_map_subtype,inf_of_le_left hUH]
  have hnormal : (Subgroup.normalizer (UH : Set H)).map H.subtype≤
      Subgroup.normalizer (U : Set _) ⊓ H := by
    intro g hg
    have hn := UH.le_normalizer_map H.subtype hg
    rw [hm] at hn
    refine ⟨hn,?_⟩
    obtain ⟨x,hx,rfl⟩ := hg
    exact x.property
  apply CFSGSylowNormalizerMaximality.sylowOfNormalizer UH hUp
  intro P hP hPN
  have hmap : P.map H.subtype≤Subgroup.normalizer (U : Set _) ⊓ H :=
    (Subgroup.map_mono hPN).trans hnormal
  have hle := pSubgroup_normalizer_le_positive A hd hs hp ho K ε hε hA hidentity p
    (P.map H.subtype) (hP.map H.subtype) (le_trans hmap inf_le_right) (le_trans hmap inf_le_left)
  intro x hx
  exact hle ⟨x,hx,rfl⟩

theorem canonicalPositiveSylow_coe (K : Type) [Field K] [Finite K]
    (ε : Fin r→ℤ) (hε : ∀i,ε i*ε i=1) (hA : ∀i j,ε i*|A i j|=A j i*ε j)
    (hidentity : ∀w : List (Fin r),wordUnit A hs hp b₀ s₀ K w∈
      Subgroup.normalizer (rootGroup A hs hp b₀ s₀ K false : Set _)→wordLinear A hs hp b₀ s₀ w=1)
    (p : ℕ) [Fact p.Prime] [CharP K p] :
    (canonicalPositiveSylow A hd hs hp ho K ε hε hA hidentity p : Subgroup (ElementaryGroup A hd hs hp ho K))=
      (rootGroup A hs hp b₀ s₀ K false).subgroupOf (ElementaryGroup A hd hs hp ho K) := rfl

end SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinatePositiveSylow
