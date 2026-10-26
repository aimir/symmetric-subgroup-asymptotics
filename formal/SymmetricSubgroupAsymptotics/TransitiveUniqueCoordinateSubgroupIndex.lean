import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.GroupTheory.Index

/-! A subgroup preserving a unique distinguished coordinate lies in
its actual point stabilizer. Coordinate transitivity supplies the full
degree index, without a full symmetric permutation image. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.TransitiveUniqueCoordinateSubgroupIndex

theorem degree_mul_card_le {G I : Type*} [Group G] [Finite G] [Finite I]
    (t : G →* Equiv.Perm I)
    (htrans : ∀ i j : I,∃g : G,t g i=j)
    (U : Subgroup G) (P : I → Prop)
    (hcard : Nat.card {i : I // P i}=1)
    (hpreserve : ∀ (g : G),g∈U → ∀ i,P (t g i) ↔ P i) :
    Nat.card I*Nat.card U≤Nat.card G := by
  letI : MulAction G I := MulAction.compHom I t
  letI : MulAction.IsPretransitive G I := ⟨htrans⟩
  letI : Subsingleton {i : I // P i} := Finite.card_le_one_iff_subsingleton.mp hcard.le
  have hnonempty : Nonempty {i : I // P i} :=
    Finite.card_pos_iff.mp (by rw [hcard]; decide)
  obtain ⟨i⟩ := hnonempty
  have hle : U≤MulAction.stabilizer G i.val := by
    intro g hg
    change t g i.val=i.val
    have hi : P (t g i.val) := (hpreserve g hg i.val).mpr i.property
    exact congrArg (fun z : {i : I // P i} => z.val)
      (Subsingleton.elim ⟨t g i.val,hi⟩ i)
  have hidx : Nat.card I≤U.index := by
    have h := Subgroup.index_antitone hle
    simpa only [MulAction.index_stabilizer_of_transitive] using h
  calc
    _≤U.index*Nat.card U := Nat.mul_le_mul_right _ hidx
    _=Nat.card G := U.index_mul_card

end SymmetricSubgroupAsymptotics.TransitiveUniqueCoordinateSubgroupIndex
