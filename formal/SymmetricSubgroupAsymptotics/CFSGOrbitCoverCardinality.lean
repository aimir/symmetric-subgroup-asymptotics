import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.GroupTheory.Index

/-! A finite group covering the orbit of another action bounds its
cardinality after the actual point stabilizer is charged. No action
faithfulness or transitivity on the whole ambient type is required. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrbitCoverCardinality
variable {G H X : Type*} [Group G] [Group H] [Finite G]
  [MulAction G X] [MulAction H X]

theorem card_le_cover_mul_stabilizer (x : X)
    (hcover : ∀ h : H, ∃ g : G, h • x = g • x) :
    Nat.card H ≤ Nat.card G * Nat.card (MulAction.stabilizer H x) := by
  let coverMap : G → MulAction.orbit G x := fun g => ⟨g • x, ⟨g, rfl⟩⟩
  have hsurj : Function.Surjective coverMap := by
    rintro ⟨y, ⟨g, hg⟩⟩
    exact ⟨g, Subtype.ext hg⟩
  letI : Finite (MulAction.orbit G x) := Finite.of_surjective coverMap hsurj
  let embed : MulAction.orbit H x → MulAction.orbit G x := fun y =>
    ⟨y.val, by
      obtain ⟨h, hh⟩ := y.property
      obtain ⟨g, hg⟩ := hcover h
      exact ⟨g, hg.symm.trans hh⟩⟩
  have hinj : Function.Injective embed := by
    intro y z he
    exact Subtype.ext (congrArg (fun z : MulAction.orbit G x => z.val) he)
  have horbit : Nat.card (MulAction.orbit H x) ≤ Nat.card G :=
    (Nat.card_le_card_of_injective embed hinj).trans
      (Nat.card_le_card_of_surjective coverMap hsurj)
  calc
    Nat.card H = Nat.card (MulAction.orbit H x) * Nat.card (MulAction.stabilizer H x) := by
      rw [← Nat.card_prod]
      exact (Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup H x)).symm
    _ ≤ Nat.card G * Nat.card (MulAction.stabilizer H x) := Nat.mul_le_mul_right _ horbit

end SymmetricSubgroupAsymptotics.CFSGOrbitCoverCardinality
