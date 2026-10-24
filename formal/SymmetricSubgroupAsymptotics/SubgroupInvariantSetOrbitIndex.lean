import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.GroupTheory.Index

/-! A full-group orbit is bounded by the orbit under an actual subgroup
and that same subgroup's index. The invariant-set corollary retains this
coupling, for example for an actual stabilizer's annihilator. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.SubgroupInvariantSetOrbitIndex

variable {G X : Type*} [Group G] [Finite G] [MulAction G X]

/-- Restricting to an actual subgroup can increase the orbit bound by at
most the index of that same subgroup. -/
theorem orbit_card_le_subgroup_orbit_mul_index (L : Subgroup G) (x : X) :
    Nat.card (MulAction.orbit G x) ≤
      Nat.card (MulAction.orbit L x) * L.index := by
  let S : Subgroup G := MulAction.stabilizer G x
  have hG : S.index = Nat.card (MulAction.orbit G x) :=
    (Nat.card_congr (MulAction.orbitEquivQuotientStabilizer G x)).symm
  have hL : S.relIndex L = Nat.card (MulAction.orbit L x) := by
    change (S.subgroupOf L).index = _
    have hs : S.subgroupOf L = MulAction.stabilizer L x := by
      ext g
      rfl
    rw [hs]
    exact (Nat.card_congr (MulAction.orbitEquivQuotientStabilizer L x)).symm
  have hle : S.index ≤ (S ⊓ L).index :=
    Nat.le_of_dvd (Nat.pos_of_ne_zero (S ⊓ L).index_ne_zero_of_finite)
      (Subgroup.index_dvd_of_le (show S ⊓ L ≤ S from inf_le_left))
  have hfactor : (S ⊓ L).index = S.relIndex L * L.index := by
    rw [← Subgroup.inf_relIndex_right S L]
    exact (Subgroup.relIndex_mul_index (show S ⊓ L ≤ L from inf_le_right)).symm
  rw [hG, hfactor, hL] at hle
  exact hle

/-- An actual invariant set containing the point bounds the restricted
orbit. The index belongs to the same subgroup preserving that set. -/
theorem orbit_card_le_invariant_set_mul_index [Finite X]
    (L : Subgroup G) (A : Set X) (x : X) (hx : x ∈ A)
    (hA : ∀ g : L, ∀ y ∈ A, g • y ∈ A) :
    Nat.card (MulAction.orbit G x) ≤ Nat.card A * L.index := by
  let f : MulAction.orbit L x → A := fun y =>
    ⟨y.val, by
      obtain ⟨g, hg⟩ := y.property
      rw [← hg]
      exact hA g x hx⟩
  have hf : Function.Injective f := by
    intro y z he
    exact Subtype.ext (congrArg (fun a : A => (a : X)) he)
  exact (orbit_card_le_subgroup_orbit_mul_index L x).trans
    (Nat.mul_le_mul_right L.index (Nat.card_le_card_of_injective f hf))

end SymmetricSubgroupAsymptotics.SubgroupInvariantSetOrbitIndex
