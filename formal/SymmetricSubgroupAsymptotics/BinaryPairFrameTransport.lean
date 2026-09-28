import SymmetricSubgroupAsymptotics.BinaryPairFramePairing
import SymmetricSubgroupAsymptotics.TransitiveBinaryPairFrame
import SymmetricSubgroupAsymptotics.OrbitProfileAssembly
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

/-- The literal kernel of every binary pair frame is a binary group.  This
uses the reversible chart into the actual correlated flip subspace, rather
than the ambient full coordinate product. -/
theorem kernel_isPGroup : IsPGroup 2 F.top.ker := by
  have hM : IsPGroup 2 (Multiplicative F.kernelSpace) := by
    intro w
    refine ⟨1, ?_⟩
    rw [pow_one]
    change 2 • w.toAdd = 0
    rw [← Nat.cast_smul_eq_nsmul (ZMod 2), ZMod.natCast_self, zero_smul]
  exact hM.of_equiv F.kernelChart.symm

/-- A binary top together with the binary pair kernel makes the entire
original physical action binary; no splitting of the extension is used. -/
theorem source_isPGroup_of_top_isPGroup
    (hTop : IsPGroup 2 F.top.range) : IsPGroup 2 U := by
  have hPreimage : IsPGroup 2 (F.top.range.comap F.top) :=
    hTop.comap_of_ker_isPGroup F.top F.kernel_isPGroup
  have htop : F.top.range.comap F.top = (⊤ : Subgroup U) := by
    apply top_unique
    intro u _
    exact ⟨u, rfl⟩
  have hTopSubgroup : IsPGroup 2 (⊤ : Subgroup U) := htop ▸ hPreimage
  exact hTopSubgroup.of_equiv Subgroup.topEquiv

theorem source_isPGroup_iff_top_isPGroup :
    IsPGroup 2 U ↔ IsPGroup 2 F.top.range :=
  ⟨F.top_isPGroup, F.source_isPGroup_of_top_isPGroup⟩

/-- Nonbinaryness of the original source is visible in the faithful pair
top, because the omitted pair kernel is always binary. -/
theorem top_not_isPGroup (hU : ¬ IsPGroup 2 U) :
    ¬ IsPGroup 2 F.top.range := by
  intro hTop
  exact hU (F.source_isPGroup_of_top_isPGroup hTop)

/-- The source-group equivalence induced by an actual relabelling of the
physical points. -/
def sourceRelabelEquiv {Y : Type*} (e : X ≃ Y) :
    U ≃* relabelSubgroup e U :=
  e.permCongrHom.subgroupMap U

/-- Move the physical points and their permutation subgroup through the same
bijection, retaining the pair labels and bit orientations. -/
def relabelPoints {Y : Type*} (e : X ≃ Y) :
    BinaryPairFrame (relabelSubgroup e U) I :=
  BinaryPairFrame.ofEquiv (sourceRelabelEquiv (U := U) e) F.top
    (F.frame.trans e) (by
      intro u p
      change
        (F.frame.symm
          (e.symm
            (e.permCongr (u : Equiv.Perm X) (e (F.frame p))))).1 =
          F.top u p.1
      simpa only [Equiv.permCongr_apply, Equiv.symm_apply_apply,
        Equiv.apply_symm_apply] using F.intertwine u p)

@[simp] theorem relabelPoints_frame {Y : Type*} (e : X ≃ Y)
    (p : I × ZMod 2) :
    (F.relabelPoints e).frame p = e (F.frame p) := rfl

@[simp] theorem relabelPoints_top_sourceRelabelEquiv {Y : Type*}
    (e : X ≃ Y) (u : U) :
    (F.relabelPoints e).top (sourceRelabelEquiv (U := U) e u) = F.top u := by
  simp only [relabelPoints, sourceRelabelEquiv, BinaryPairFrame.ofEquiv,
    MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    MulEquiv.symm_apply_apply]

/-- Point relabelling leaves the literal pair top subgroup unchanged. -/
theorem relabelPoints_top_range {Y : Type*} (e : X ≃ Y) :
    (F.relabelPoints e).top.range = F.top.range := by
  apply le_antisymm
  · rintro q ⟨u, rfl⟩
    obtain ⟨v, rfl⟩ := (sourceRelabelEquiv (U := U) e).surjective u
    exact ⟨v, (F.relabelPoints_top_sourceRelabelEquiv e v).symm⟩
  · rintro q ⟨u, rfl⟩
    exact ⟨sourceRelabelEquiv (U := U) e u,
      F.relabelPoints_top_sourceRelabelEquiv e u⟩

/-- The transported partner involution is the pointwise conjugate of the
original physical pairing. -/
@[simp] theorem relabelPoints_partnerMap {Y : Type*} (e : X ≃ Y)
    (x : X) :
    (F.relabelPoints e).partnerMap (e x) = e (F.partnerMap x) := by
  obtain ⟨⟨i, b⟩, rfl⟩ := F.frame.surjective x
  rw [show e (F.frame (i, b)) = (F.relabelPoints e).frame (i, b) by rfl]
  rw [(F.relabelPoints e).partnerMap_frame, F.partnerMap_frame,
    F.relabelPoints_frame]

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
