import SymmetricSubgroupAsymptotics.SubgroupInvariantSetOrbitIndex
import Mathlib.Algebra.Group.Action.End
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Linarith

/-! A nonzero additive subgroup, invariant under an actual subgroup of
an automorphism group transitive on nonzero vectors, controls that SAME
subgroup's index. No coefficient-field linearity is required. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.AdditiveNonzeroOrbitIndex

variable {G V : Type*} [Group G] [AddGroup V]

theorem nonzero_card [Finite V] :
    Nat.card {v : V // v ≠ 0} = Nat.card V - 1 := by
  classical
  letI : Fintype V := Fintype.ofFinite V
  simpa only [Nat.card_eq_fintype_card, Fintype.card_subtype_eq] using
    (Fintype.card_subtype_compl (fun v : V => v = 0))

variable [MulAction G V]

theorem nonzero_orbit_card_eq [Finite V]
    (hzero : ∀ g : G, g • (0 : V) = 0)
    (htrans : ∀ v w : V, v ≠ 0 → w ≠ 0 → ∃ g : G, g • v = w)
    (v : V) (hv : v ≠ 0) :
    Nat.card (MulAction.orbit G v) = Nat.card V - 1 := by
  have he : MulAction.orbit G v = {w : V | w ≠ 0} := by
    ext w
    constructor
    · rintro ⟨g, hg⟩ hw
      apply hv
      apply MulAction.injective g
      change g • v = w at hg
      exact (hg.trans hw).trans (hzero g).symm
    · intro hw
      obtain ⟨g, hg⟩ := htrans v w hv hw
      exact ⟨g, hg⟩
  rw [he]
  exact nonzero_card

/-- The same invariant subgroup W and the same actual subgroup L occur
in the cardinal and index factors. W need only be an additive subgroup. -/
theorem card_sub_one_le_subgroup_card_sub_one_mul_index [Finite G] [Finite V]
    (hzero : ∀ g : G, g • (0 : V) = 0)
    (htrans : ∀ v w : V, v ≠ 0 → w ≠ 0 → ∃ g : G, g • v = w)
    (L : Subgroup G) (W : AddSubgroup V)
    (hW : ∀ g ∈ L, ∀ w ∈ W, g • w ∈ W)
    (v : V) (hvW : v ∈ W) (hv : v ≠ 0) :
    Nat.card V - 1 ≤ (Nat.card W - 1) * L.index := by
  let f : MulAction.orbit L v → {w : W // w ≠ 0} := fun w =>
    ⟨⟨w.val, by
      obtain ⟨g, hg⟩ := w.property
      rw [← hg]
      exact hW g.val g.property v hvW⟩, by
      intro hw
      obtain ⟨g, hg⟩ := w.property
      apply hv
      apply MulAction.injective g.val
      change g.val • v = w.val at hg
      have hw' : w.val = 0 := congrArg (fun z : W => (z : V)) hw
      exact (hg.trans hw').trans (hzero g.val).symm⟩
  have hf : Function.Injective f := by
    intro w z he
    apply Subtype.ext
    exact congrArg (fun x : {w : W // w ≠ 0} => ((x.val : W) : V)) he
  have hcard : Nat.card (MulAction.orbit L v) ≤ Nat.card W - 1 := by
    calc
      _ ≤ Nat.card {w : W // w ≠ 0} := Nat.card_le_card_of_injective f hf
      _ = _ := nonzero_card
  calc
    Nat.card V - 1 = Nat.card (MulAction.orbit G v) :=
      (nonzero_orbit_card_eq hzero htrans v hv).symm
    _ ≤ Nat.card (MulAction.orbit L v) * L.index :=
      SubgroupInvariantSetOrbitIndex.orbit_card_le_subgroup_orbit_mul_index L v
    _ ≤ (Nat.card W - 1) * L.index := Nat.mul_le_mul_right L.index hcard

/-- A slightly weaker form avoids subtraction and is convenient when
an independent isotropy argument already bounds the size of W. -/
theorem card_le_subgroup_card_mul_index [Finite G] [Finite V]
    (hzero : ∀ g : G, g • (0 : V) = 0)
    (htrans : ∀ v w : V, v ≠ 0 → w ≠ 0 → ∃ g : G, g • v = w)
    (L : Subgroup G) (W : AddSubgroup V)
    (hW : ∀ g ∈ L, ∀ w ∈ W, g • w ∈ W)
    (v : V) (hvW : v ∈ W) (hv : v ≠ 0) :
    Nat.card V ≤ Nat.card W * L.index := by
  have h := card_sub_one_le_subgroup_card_sub_one_mul_index hzero htrans L W hW v hvW hv
  have hV : 0 < Nat.card V := Nat.card_pos
  have hWpos : 0 < Nat.card W := Nat.card_pos
  have hL : 0 < L.index := Nat.card_pos (α := G ⧸ L)
  have hVsub := Nat.sub_add_cancel (show 1 ≤ Nat.card V by omega)
  have hWsub := Nat.sub_add_cancel (show 1 ≤ Nat.card W by omega)
  nlinarith

end SymmetricSubgroupAsymptotics.AdditiveNonzeroOrbitIndex
