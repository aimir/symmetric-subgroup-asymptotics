import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateOppositeWeylIntersection
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateElementaryRootParameters

/-! The full-normalizer/simple-root intersection inside the SAME actual
elementary matrix group, ready for central-quotient transport. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateElementaryNormalizerIntersection
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing
open CFSGNormTwoGeckIntegralRealization CFSGNormTwoGeckPositivePGroup
open CFSGSerreQuadraticMatrix CFSGNormTwoCoordinateElementaryRootParameters
open CFSGNormTwoCoordinateOppositeNormalizerIntersection
open CFSGNormTwoCoordinateOppositeWeylIntersection
open CFSGNormTwoGeckWeylWordDegree CFSGNormTwoGeckWeylLatticeLinear
variable {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ) (hd : ∀j,A j j=2)
    (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    (ho : ∀i j,i≠j→A i j≤0)
    [Fintype (Roots A)] [DecidableEq (Roots A)]
    [(rootPairing A hs hp).IsIrreducible]
local notation "b₀" => coordinateBase A hd hs hp ho
local notation "s₀" => coordinateIndexEquiv A hd hs hp ho
local notation "D" => realizationData A hs hp b₀ s₀

theorem elementary_negative_weyl_join_eq_root_join (K : Type) [Field K] (i : Fin r) :
    Subgroup.normalizer ((rootGroup A hs hp b₀ s₀ K true).subgroupOf
      (ElementaryGroup A hd hs hp ho K) : Set _)⊔
      (Subgroup.closure {canonicalWeyl D K i}).subgroupOf (ElementaryGroup A hd hs hp ho K)=
    Subgroup.normalizer ((rootGroup A hs hp b₀ s₀ K true).subgroupOf
      (ElementaryGroup A hd hs hp ho K) : Set _)⊔
      (canonicalRootSubgroup D K false i).subgroupOf (ElementaryGroup A hd hs hp ho K) := by
  let H := ElementaryGroup A hd hs hp ho K
  let V := rootGroup A hs hp b₀ s₀ K true
  let U := rootGroup A hs hp b₀ s₀ K false
  have hjoin : U⊔V=H := positive_sup_negative A hs hp b₀ s₀ K
  have hVH : V≤H := by rw [←hjoin]; exact le_sup_right
  have hRH : canonicalRootSubgroup D K false i≤H := by
    rintro g ⟨t,rfl⟩
    exact (canonicalElementaryRoot D K false i t).property
  have hWH : Subgroup.closure {canonicalWeyl D K i}≤H := by
    apply (Subgroup.closure_le _).mpr
    rintro g (rfl : g=canonicalWeyl D K i)
    simpa only [wordUnit,mul_one] using CFSGNormTwoGeckRootWordMembership.word_mem
      A hs hp b₀ s₀ K [i]
  have hh := congrArg (fun S=>S.subgroupOf H)
    (negative_normalizer_weyl_join_eq_simple_join A hd hs hp ho K i)
  change ((Subgroup.normalizer (V : Set _)⊓H)⊔
      Subgroup.closure {canonicalWeyl D K i}).subgroupOf H=
    ((Subgroup.normalizer (V : Set _)⊓H)⊔canonicalRootSubgroup D K false i).subgroupOf H at hh
  rw [Subgroup.subgroupOf_sup inf_le_right hWH,Subgroup.subgroupOf_sup inf_le_right hRH,
    Subgroup.inf_subgroupOf_right,Subgroup.subgroupOf_normalizer_eq hVH] at hh
  exact hh

theorem elementary_opposite_normalizer_intersection (K : Type) [Field K]
    (ε : Fin r→ℤ) (hε : ∀j,ε j*ε j=1) (hA : ∀i j,ε i*|A i j|=A j i*ε j)
    (hidentity : ∀w : List (Fin r),wordUnit A hs hp b₀ s₀ K w∈
      Subgroup.normalizer (rootGroup A hs hp b₀ s₀ K false : Set _)→wordLinear A hs hp b₀ s₀ w=1)
    (i : Fin r) :
    (rootGroup A hs hp b₀ s₀ K false).subgroupOf (ElementaryGroup A hd hs hp ho K) ⊓
      (Subgroup.normalizer ((rootGroup A hs hp b₀ s₀ K true).subgroupOf
        (ElementaryGroup A hd hs hp ho K) : Set _)⊔
        (canonicalRootSubgroup D K false i).subgroupOf (ElementaryGroup A hd hs hp ho K))=
      (canonicalRootSubgroup D K false i).subgroupOf (ElementaryGroup A hd hs hp ho K) := by
  let H := ElementaryGroup A hd hs hp ho K
  let U := rootGroup A hs hp b₀ s₀ K false
  let V := rootGroup A hs hp b₀ s₀ K true
  let R := canonicalRootSubgroup D K false i
  let NH := Subgroup.normalizer (V.subgroupOf H : Set H)
  let N := Subgroup.normalizer (V : Set _)⊓H
  have hjoin : U⊔V=H := positive_sup_negative A hs hp b₀ s₀ K
  have hVH : V≤H := by rw [←hjoin]; exact le_sup_right
  have hRH : R≤H := by
    rintro g ⟨t,rfl⟩
    exact (canonicalElementaryRoot D K false i t).property
  have hVmap : (V.subgroupOf H).map H.subtype=V := Subgroup.map_subgroupOf_eq_of_le hVH
  have hRmap : (R.subgroupOf H).map H.subtype=R := Subgroup.map_subgroupOf_eq_of_le hRH
  have hNmap : NH.map H.subtype≤N := by
    rintro _ ⟨g,hg,rfl⟩
    have hn := Subgroup.le_normalizer_map H.subtype
      (show g.val∈NH.map H.subtype from ⟨g,hg,rfl⟩)
    rw [hVmap] at hn
    exact ⟨hn,g.property⟩
  apply le_antisymm
  · intro g hg
    have hx : g.val∈NH.map H.subtype⊔R := by
      rw [←hRmap,←Subgroup.map_sup]
      exact ⟨g,hg.2,rfl⟩
    have hbound : NH.map H.subtype⊔R≤N⊔R := sup_le
      (hNmap.trans le_sup_left) le_sup_right
    have hm : g.val∈U⊓(N⊔R) := ⟨hg.1,hbound hx⟩
    rw [opposite_normalizer_parabolic_intersection A hd hs hp ho K ε hε hA hidentity i] at hm
    exact hm
  · apply le_inf _ le_sup_right
    rintro g ⟨t,ht⟩
    exact Subgroup.subset_closure ⟨(i,t),ht⟩

end SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateElementaryNormalizerIntersection
