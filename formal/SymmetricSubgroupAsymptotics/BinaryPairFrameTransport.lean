import SymmetricSubgroupAsymptotics.BinaryPairFramePairing
import SymmetricSubgroupAsymptotics.TransitiveBinaryPairFrame
import Mathlib.Data.Finite.Card

/-!
# Original pair-frame tops and reindexing

Every top below is the range of the supplied original frame's action.
Reindexing changes only the pair labels, preserving the original points,
the original permutation subgroup and the literal partner involution.
The existence theorem uses an actual original point-stabilizer cover.
-/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics

namespace BinaryPairFrame

variable {X I J : Type*} {U : Subgroup (Equiv.Perm X)} (F : BinaryPairFrame U I)

include F in
/-- The pair labels inject into the original points by choosing bit zero. -/
theorem index_finite [Finite X] : Finite I := by
  apply Finite.of_injective (fun i : I => F.frame (i,0))
  intro i j h
  exact congrArg Prod.fst (F.frame.injective h)

include F in
/-- The degree identity is for this actual frame on the original points. -/
theorem card_points : Nat.card X = 2 * Nat.card I := by
  calc
    Nat.card X = Nat.card (I × ZMod 2) := (Nat.card_congr F.frame).symm
    _ = 2 * Nat.card I := by rw [Nat.card_prod, Nat.card_zmod, Nat.mul_comm]

/-- Original transitivity passes to the literal top range of any frame. -/
theorem top_pretransitive [MulAction.IsPretransitive U X] :
    MulAction.IsPretransitive F.top.range I := by
  constructor
  intro i j
  obtain ⟨u,hu⟩ := MulAction.exists_smul_eq U (F.frame (i,0)) (F.frame (j,0))
  refine ⟨F.top.rangeRestrict u, ?_⟩
  change F.top u i = j
  have hi := F.intertwine u (i,0)
  change (F.frame.symm (u • F.frame (i,0))).1 = F.top u i at hi
  rw [hu, Equiv.symm_apply_apply] at hi
  exact hi.symm

/-- The top remains binary as the actual image of the original source. -/
theorem top_isPGroup (hU : IsPGroup 2 U) : IsPGroup 2 F.top.range :=
  hU.of_surjective F.top.rangeRestrict F.top.rangeRestrict_surjective

/-- Change only the pair index, using the same original frame points. -/
def reindex (e : I ≃ J) : BinaryPairFrame U J where
  frame := (Equiv.prodCongr e.symm (Equiv.refl (ZMod 2))).trans F.frame
  top := e.permCongrHom.toMonoidHom.comp F.top
  intertwine u p := by
    change e ((F.frame.symm ((u : Equiv.Perm X)
      (F.frame (e.symm p.1,p.2)))).1) = e (F.top u (e.symm p.1))
    exact congrArg e (F.intertwine u (e.symm p.1,p.2))

@[simp] theorem reindex_frame (e : I ≃ J) (j : J) (b : ZMod 2) :
    (F.reindex e).frame (j,b) = F.frame (e.symm j,b) := rfl

@[simp] theorem reindex_top_apply (e : I ≃ J) (u : U) (j : J) :
    (F.reindex e).top u j = e (F.top u (e.symm j)) := rfl

/-- Pair labels do not alter the literal original partner function. -/
theorem reindex_partnerMap (e : I ≃ J) :
    (F.reindex e).partnerMap = F.partnerMap := by
  funext x
  change F.frame (e.symm (e ((F.frame.symm x).1)), (F.frame.symm x).2+1) =
    F.frame ((F.frame.symm x).1, (F.frame.symm x).2+1)
  rw [e.symm_apply_apply]

@[simp] theorem reindex_underlyingPairing (e : I ≃ J) :
    (F.reindex e).underlyingPairing = F.underlyingPairing :=
  Subtype.ext (F.reindex_partnerMap e)

end BinaryPairFrame

/-- A degree-2^(k+1) original transitive binary action has an actual pair
frame indexed by Fin(2^k). Only the original cover's pair labels change. -/
theorem transitiveBinaryPairFrame_nonempty
    {X : Type} [Finite X] (k : ℕ) (U : Subgroup (Equiv.Perm X))
    [MulAction.IsPretransitive U X] (hU : IsPGroup 2 U)
    (hdegree : Nat.card X = 2^(k+1)) :
    Nonempty (BinaryPairFrame U (Fin (2^k))) := by
  letI : Nontrivial X := Finite.one_lt_card_iff_nontrivial.mp (by
    rw [hdegree, pow_succ]
    have hp : 0 < 2^k := pow_pos (by decide) _
    omega)
  obtain ⟨D⟩ := transitiveBinaryPairCover_nonempty U hU
    (Classical.choice (inferInstance : Nonempty X))
  have hcard : Nat.card D.Points = 2^k := by
    have hd := D.degree_product
    rw [hdegree, pow_succ] at hd
    omega
  exact ⟨D.frame.reindex (Finite.equivFinOfCardEq hcard)⟩

/-- The finite family of distinct realized original pairings is nonempty.
No auxiliary chart is added to the family's counted values. -/
theorem transitiveBinaryRealizedPairing_nonempty
    {X : Type} [Finite X] (k : ℕ) (U : Subgroup (Equiv.Perm X))
    [MulAction.IsPretransitive U X] (hU : IsPGroup 2 U)
    (hdegree : Nat.card X = 2^(k+1)) :
    Nonempty (RealizedPairing U (Fin (2^k))) := by
  obtain ⟨F⟩ := transitiveBinaryPairFrame_nonempty k U hU hdegree
  exact ⟨F.realizedPairing⟩

end SymmetricSubgroupAsymptotics

end
