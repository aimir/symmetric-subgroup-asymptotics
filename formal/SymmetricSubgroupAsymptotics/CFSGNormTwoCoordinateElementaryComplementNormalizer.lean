import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinatePositiveWeylJoin
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateElementaryRootParameters

/-! The complement normalizer identity in the ACTUAL elementary group,
with the full positive normalizer and literal negative-root subgroup. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateElementaryComplementNormalizer
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing CFSGSerreQuadraticMatrix
open CFSGNormTwoGeckIntegralRealization CFSGNormTwoGeckPositivePGroup
open CFSGNormTwoGeckPositiveComplement CFSGNormTwoCoordinateElementaryRootParameters
open CFSGNormTwoCoordinateComplementNormalizer CFSGNormTwoCoordinatePositiveWeylJoin
open CFSGNormTwoGeckWeylWordDegree CFSGNormTwoGeckWeylLatticeLinear
variable {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ) (hd : ∀j,A j j=2)
    (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    (ho : ∀i j,i≠j→A i j≤0)
    [Fintype (Roots A)] [DecidableEq (Roots A)]
    [(rootPairing A hs hp).IsReduced] [(rootPairing A hs hp).IsIrreducible]
    (K : Type) [Field K] [Finite K]
local notation "b₀" => coordinateBase A hd hs hp ho
local notation "s₀" => coordinateIndexEquiv A hd hs hp ho
local notation "D" => realizationData A hs hp b₀ s₀

theorem elementary_complement_normalizer
    (ε : Fin r→ℤ) (hε : ∀j,ε j*ε j=1) (hA : ∀i j,ε i*|A i j|=A j i*ε j)
    (hidentity : ∀w : List (Fin r),wordUnit A hs hp b₀ s₀ K w∈
      Subgroup.normalizer (rootGroup A hs hp b₀ s₀ K false : Set _)→wordLinear A hs hp b₀ s₀ w=1)
    (i : Fin r) :
    Subgroup.normalizer ((positiveComplement A hs hp b₀ s₀ K i).subgroupOf
      (ElementaryGroup A hd hs hp ho K) : Set _)=
      Subgroup.normalizer ((rootGroup A hs hp b₀ s₀ K false).subgroupOf
        (ElementaryGroup A hd hs hp ho K) : Set _)⊔
        (canonicalRootSubgroup D K true i).subgroupOf (ElementaryGroup A hd hs hp ho K) := by
  let H := ElementaryGroup A hd hs hp ho K
  let U := rootGroup A hs hp b₀ s₀ K false
  let M := positiveComplement A hs hp b₀ s₀ K i
  let R := canonicalRootSubgroup D K true i
  have hjoin : U⊔rootGroup A hs hp b₀ s₀ K true=H := positive_sup_negative A hs hp b₀ s₀ K
  have hUH : U≤H := by rw [←hjoin];exact le_sup_left
  have hMH : M≤H := (complement_le_positive A hs hp b₀ s₀ K i).trans hUH
  have hRH : R≤H := by
    rintro g ⟨t,rfl⟩
    exact (canonicalElementaryRoot D K true i t).property
  have hmapM : (Subgroup.normalizer (M.subgroupOf H : Set H)).map H.subtype=
      Subgroup.normalizer (M : Set _)⊓H := by
    rw [←Subgroup.subgroupOf_normalizer_eq hMH,Subgroup.subgroupOf_map_subtype]
  have hmapU : (Subgroup.normalizer (U.subgroupOf H : Set H)).map H.subtype=
      Subgroup.normalizer (U : Set _)⊓H := by
    rw [←Subgroup.subgroupOf_normalizer_eq hUH,Subgroup.subgroupOf_map_subtype]
  apply Subgroup.map_injective H.subtype_injective
  rw [Subgroup.map_sup,hmapM,hmapU,Subgroup.map_subgroupOf_eq_of_le hRH]
  exact (complement_normalizer_eq_rank_one A hd hs hp ho K ε hε hA hidentity i).trans
    (positive_normalizer_weyl_join_eq_negative_join A hd hs hp ho K i)

end SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateElementaryComplementNormalizer
