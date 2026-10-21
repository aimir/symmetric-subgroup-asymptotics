import SymmetricSubgroupAsymptotics.BinaryPairFrameEquivariance
import SymmetricSubgroupAsymptotics.BinaryPairFrameTransport
import Mathlib.Data.Fin.Tuple.Basic

/-! Coordinates for an actual binary action in which coordinate j has
translation displacement depending only on lower coordinates. Actual
tower elements toggle a selected bit and fix lower bits; higher errors
are unrestricted. No regular elementary subgroup is asserted. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics

structure BinaryTriangularPointCoordinates (G X : Type) [Group G] [MulAction G X] (n : ℕ) where
  pointEquiv : X ≃ (Fin n → ZMod 2)
  displacement : ∀ (g : G) (i : Fin n) (x y : X),
    (∀ j : Fin n, j < i → pointEquiv x j = pointEquiv y j) →
    pointEquiv (g • x) i - pointEquiv x i = pointEquiv (g • y) i - pointEquiv y i
  flip : ∀ i : Fin n, ∃ g : G, ∀ x : X,
    (∀ j : Fin n, j < i → pointEquiv (g • x) j = pointEquiv x j) ∧
    pointEquiv (g • x) i = pointEquiv x i + 1

namespace BinaryTriangularPointCoordinates

def snocEquiv (n : ℕ) : ((Fin n → ZMod 2) × ZMod 2) ≃ (Fin (n+1) → ZMod 2) where
  toFun p := Fin.snoc p.1 p.2
  invFun f := (fun i => f i.castSucc, f (Fin.last n))
  left_inv p := by
    apply Prod.ext
    · funext i
      change Fin.snoc (α := fun _ => ZMod 2) p.1 p.2 i.castSucc = p.1 i
      exact Fin.snoc_castSucc (α := fun _ => ZMod 2) p.2 p.1 i
    · change Fin.snoc (α := fun _ => ZMod 2) p.1 p.2 (Fin.last n) = p.2
      exact Fin.snoc_last (α := fun _ => ZMod 2) p.2 p.1
  right_inv f := by
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · exact Fin.snoc_last _ _
    · exact Fin.snoc_castSucc _ _ _

variable {X : Type} {U : Subgroup (Equiv.Perm X)} {n : ℕ}
    (F : BinaryPairFrame U (Fin (2^n)))
    (T : BinaryTriangularPointCoordinates F.top.range (Fin (2^n)) n)

def pairPointEquiv : X ≃ (Fin (n+1) → ZMod 2) :=
  F.frame.symm.trans ((Equiv.prodCongr T.pointEquiv (Equiv.refl (ZMod 2))).trans (snocEquiv n))

@[simp] theorem pairPointEquiv_low (x : X) (j : Fin n) :
    pairPointEquiv F T x j.castSucc = T.pointEquiv (F.frame.symm x).1 j := by
  change Fin.snoc (α := fun _ => ZMod 2)
    (T.pointEquiv (F.frame.symm x).1) (F.frame.symm x).2 j.castSucc =
      T.pointEquiv (F.frame.symm x).1 j
  exact Fin.snoc_castSucc (α := fun _ => ZMod 2)
    (F.frame.symm x).2 (T.pointEquiv (F.frame.symm x).1) j

@[simp] theorem pairPointEquiv_last (x : X) :
    pairPointEquiv F T x (Fin.last n) = (F.frame.symm x).2 := by
  change Fin.snoc (α := fun _ => ZMod 2)
    (T.pointEquiv (F.frame.symm x).1) (F.frame.symm x).2 (Fin.last n) =
      (F.frame.symm x).2
  exact Fin.snoc_last (α := fun _ => ZMod 2)
    (F.frame.symm x).2 (T.pointEquiv (F.frame.symm x).1)

private theorem action_pair (u : U) (x : X) :
    F.frame.symm (u • x) =
      (F.top u (F.frame.symm x).1, (F.frame.symm x).2 + F.offset u (F.frame.symm x).1) := by
  have h := F.action_coordinates u (F.frame.symm x).1 (F.frame.symm x).2
  simpa only [Prod.eta, Equiv.apply_symm_apply] using h

@[simp] theorem pairPointEquiv_low_action (u : U) (x : X) (j : Fin n) :
    pairPointEquiv F T (u • x) j.castSucc =
      T.pointEquiv (F.top u (F.frame.symm x).1) j := by
  rw [pairPointEquiv_low, action_pair]

theorem pairPointEquiv_last_displacement (u : U) (x : X) :
    pairPointEquiv F T (u • x) (Fin.last n) - pairPointEquiv F T x (Fin.last n) =
      F.offset u (F.frame.symm x).1 := by
  rw [pairPointEquiv_last, pairPointEquiv_last, action_pair]
  exact add_sub_cancel_left _ _

/-- A central actual pair flip extends the actual top's triangular tower. -/
def ofPairFrame (z : F.top.ker) (hz : ∀ i, F.bits z i = 1) :
    BinaryTriangularPointCoordinates U X (n+1) where
  pointEquiv := pairPointEquiv F T
  displacement := by
    intro u i
    refine Fin.lastCases ?_ (fun k => ?_) i
    · intro x y hprefix
      have hbase : (F.frame.symm x).1 = (F.frame.symm y).1 := by
        apply T.pointEquiv.injective
        funext j
        have h := hprefix j.castSucc (Fin.castSucc_lt_last j)
        simpa only [pairPointEquiv_low] using h
      rw [pairPointEquiv_last_displacement, pairPointEquiv_last_displacement, hbase]
    · intro x y hprefix
      rw [pairPointEquiv_low_action, pairPointEquiv_low,
        pairPointEquiv_low_action, pairPointEquiv_low]
      apply T.displacement (F.top.rangeRestrict u) k
      intro j hj
      have h := hprefix j.castSucc hj
      simpa only [pairPointEquiv_low] using h
  flip := by
    intro i
    refine Fin.lastCases ?_ (fun k => ?_) i
    · refine ⟨(z : U), ?_⟩
      intro x
      have hp : F.frame.symm ((z : U) • x) = ((F.frame.symm x).1, (F.frame.symm x).2 + 1) := by
        have h := F.kernel_action z (F.frame.symm x).1 (F.frame.symm x).2
        simpa only [Prod.eta, Equiv.apply_symm_apply, hz] using h
      constructor
      · intro j hj
        have hjn : j.val < n := hj
        let k : Fin n := ⟨j.val, hjn⟩
        have he : j = k.castSucc := Fin.ext rfl
        rw [he, pairPointEquiv_low, pairPointEquiv_low, hp]
      · rw [pairPointEquiv_last, pairPointEquiv_last, hp]
    · obtain ⟨t, ht⟩ := T.flip k
      obtain ⟨u, hu⟩ := F.top.rangeRestrict_surjective t
      have heq : F.top u = t.val := congrArg Subtype.val hu
      refine ⟨u, ?_⟩
      intro x
      constructor
      · intro j hj
        have hjn : j.val < n := lt_trans hj k.isLt
        let l : Fin n := ⟨j.val, hjn⟩
        have he : j = l.castSucc := Fin.ext rfl
        rw [he, pairPointEquiv_low_action, pairPointEquiv_low, heq]
        exact (ht (F.frame.symm x).1).1 l hj
      · rw [pairPointEquiv_low_action, pairPointEquiv_low, heq]
        exact (ht (F.frame.symm x).1).2

end BinaryTriangularPointCoordinates
end SymmetricSubgroupAsymptotics
