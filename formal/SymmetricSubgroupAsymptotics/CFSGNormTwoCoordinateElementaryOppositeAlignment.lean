import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateOppositeAlignment
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateElementaryRootParameters
import SymmetricSubgroupAsymptotics.CFSGSubgroupConjugateRestriction

/-! Opposite alignment inside the actual elementary matrix group, with
the conjugator retained in its literal Borel subgroup. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateElementaryOppositeAlignment
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing
open CFSGNormTwoGeckIntegralRealization CFSGNormTwoGeckPositivePGroup
open CFSGNormTwoCoordinateElementaryRootParameters CFSGNormTwoGeckBorelEnvelope
open CFSGNormTwoCoordinateOppositeAlignment CFSGSubgroupConjugateRestriction
variable {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ) (hd : ∀j,A j j=2)
    (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    (ho : ∀i j,i≠j→A i j≤0)
    [Fintype (Roots A)] [DecidableEq (Roots A)]
    [(rootPairing A hs hp).IsReduced] [(rootPairing A hs hp).IsIrreducible]
local notation "b₀" => coordinateBase A hd hs hp ho
local notation "s₀" => coordinateIndexEquiv A hd hs hp ho

theorem elementary_opposite_conjugate_by_borel (K : Type) [Field K] [Finite K]
    (g : ElementaryGroup A hd hs hp ho K)
    (hdisj : (rootGroup A hs hp b₀ s₀ K false).subgroupOf (ElementaryGroup A hd hs hp ho K) ⊓
      ((rootGroup A hs hp b₀ s₀ K false).subgroupOf (ElementaryGroup A hd hs hp ho K)).map
        (MulAut.conj g).toMonoidHom=⊥) :
    ∃b∈(borelEnvelope A hs hp b₀ s₀ K).subgroupOf (ElementaryGroup A hd hs hp ho K),
      ((rootGroup A hs hp b₀ s₀ K false).subgroupOf (ElementaryGroup A hd hs hp ho K)).map
        (MulAut.conj g).toMonoidHom=
      ((rootGroup A hs hp b₀ s₀ K true).subgroupOf (ElementaryGroup A hd hs hp ho K)).map
        (MulAut.conj b).toMonoidHom := by
  let H := ElementaryGroup A hd hs hp ho K
  let U := rootGroup A hs hp b₀ s₀ K false
  let V := rootGroup A hs hp b₀ s₀ K true
  have hjoin : U⊔V=H := positive_sup_negative A hs hp b₀ s₀ K
  have hUH : U≤H := by rw [←hjoin]; exact le_sup_left
  have hVH : V≤H := by rw [←hjoin]; exact le_sup_right
  have hUmap : (U.subgroupOf H).map H.subtype=U :=
    Subgroup.map_subgroupOf_eq_of_le hUH
  have hVmap : (V.subgroupOf H).map H.subtype=V :=
    Subgroup.map_subgroupOf_eq_of_le hVH
  have hmatrix : U⊓U.map (MulAut.conj g.val).toMonoidHom=⊥ := by
    have hh := congrArg (fun S : Subgroup H=>S.map H.subtype) hdisj
    dsimp only at hh
    rw [Subgroup.map_inf _ _ _ H.subtype_injective,Subgroup.map_bot,
      map_conjugate,hUmap] at hh
    exact hh
  obtain ⟨b,hb,he⟩ := opposite_conjugate_by_borel A hd hs hp ho K g.val g.property hmatrix
  let bH : H := ⟨b,borelEnvelope_le_canonical A hs hp b₀ s₀ K hb⟩
  refine ⟨bH,hb,?_⟩
  apply Subgroup.map_injective H.subtype_injective
  rw [map_conjugate,map_conjugate,hUmap,hVmap]
  exact he

end SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateElementaryOppositeAlignment
