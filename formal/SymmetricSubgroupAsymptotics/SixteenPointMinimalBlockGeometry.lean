import SymmetricSubgroupAsymptotics.OriginalMinimalBlock
import SymmetricSubgroupAsymptotics.ActualBlockWreathEmbedding
import SymmetricSubgroupAsymptotics.BinaryPairFrames

/-!
An actual transitive sixteen-point action is primitive or has an actual
minimal block of size two, four or eight. The two-point branch constructs
the physical binary pair frame from the same original block map. This is
an exhaustive geometric reduction, independent of finite top catalogues.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace OriginalMinimalBlock

variable {X : Type} [Finite X] {T : Subgroup (Equiv.Perm X)}
  [MulAction.IsPretransitive T X] {x : X}
  (D : OriginalMinimalBlock (A := T) x)

/-- The cardinal product is on the original fibre and original block set. -/
theorem degree_sixteen_alternatives (hX : Nat.card X = 16) :
    (Nat.card D.Fibre = 2 ∧ Nat.card D.Points = 8) ∨
    (Nat.card D.Fibre = 4 ∧ Nat.card D.Points = 4) ∨
    (Nat.card D.Fibre = 8 ∧ Nat.card D.Points = 2) := by
  let r := Nat.card D.Fibre
  let s := Nat.card D.Points
  have hr : 2 ≤ r := D.degrees_ge_two.1
  have hs : 2 ≤ s := D.degrees_ge_two.2
  have hrs : r * s = 16 := D.degree_product.trans hX
  have hr8 : r ≤ 8 := by nlinarith
  change (r = 2 ∧ s = 8) ∨ (r = 4 ∧ s = 4) ∨ (r = 8 ∧ s = 2)
  interval_cases r <;> omega

private def bitToFibre (hr : Nat.card D.Fibre = 2) : ZMod 2 ≃ D.Fibre :=
  (ZMod.finEquiv 2).symm.toEquiv.trans (Finite.equivFinOfCardEq hr).symm

private def pairCoordinates (hr : Nat.card D.Fibre = 2) :
    D.Points × ZMod 2 ≃ X :=
  ((Equiv.prodCongr (Equiv.refl D.Points) (D.bitToFibre hr)).trans
    (Equiv.prodComm D.Points D.Fibre)).trans
      (ActualBlockWreathEmbedding.productEquiv D.map D.map_equivariant D.base)

private theorem pairCoordinates_symm_first (hr : Nat.card D.Fibre = 2) (y : X) :
    ((D.pairCoordinates hr).symm y).1 = D.map y := rfl

/-- The actual pair kernel is the kernel of the original block action,
with no replacement action or loss of point coordinates. -/
def binaryPairFrame (hr : Nat.card D.Fibre = 2) : BinaryPairFrame T D.Points where
  frame := D.pairCoordinates hr
  top := D.topMap
  intertwine u p := by
    change ((D.pairCoordinates hr).symm (u • D.pairCoordinates hr p)).1 =
      D.topMap u p.1
    rw [D.pairCoordinates_symm_first]
    change D.map (u • D.pairCoordinates hr p) = u • p.1
    rw [D.map_equivariant]
    apply congrArg (fun i : D.Points => u • i)
    exact (D.pairCoordinates_symm_first hr (D.pairCoordinates hr p)).symm.trans
      (congrArg Prod.fst ((D.pairCoordinates hr).symm_apply_apply p))

@[simp] theorem binaryPairFrame_top (hr : Nat.card D.Fibre = 2) :
    (D.binaryPairFrame hr).top = D.topMap := rfl

end OriginalMinimalBlock

/-- Each imprimitive constructor retains the original minimal block, so
later local affine/semisimple arguments use its actual primitive component. -/
inductive SixteenPointMinimalBlockGeometry {X : Type} [Finite X]
    (T : Subgroup (Equiv.Perm X)) [MulAction.IsPretransitive T X] : Type 1 where
  | primitive (h : MulAction.IsPreprimitive T X)
  | pair (x : X) (D : OriginalMinimalBlock (A := T) x)
      (fibre : Nat.card D.Fibre = 2) (points : Nat.card D.Points = 8)
  | four (x : X) (D : OriginalMinimalBlock (A := T) x)
      (fibre : Nat.card D.Fibre = 4) (points : Nat.card D.Points = 4)
  | eight (x : X) (D : OriginalMinimalBlock (A := T) x)
      (fibre : Nat.card D.Fibre = 8) (points : Nat.card D.Points = 2)

/-- Exhaustive selection from the actual action, rather than a finite-list
coverage premise. The local classification remains separate. -/
noncomputable def sixteenPointMinimalBlockGeometry {X : Type} [Finite X]
    (T : Subgroup (Equiv.Perm X)) [MulAction.IsPretransitive T X]
    (hX : Nat.card X = 16) : SixteenPointMinimalBlockGeometry T := by
  by_cases hp : MulAction.IsPreprimitive T X
  · exact .primitive hp
  letI : Nontrivial X := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  let x : X := Classical.choice inferInstance
  let D : OriginalMinimalBlock (A := T) x :=
    Classical.choice (originalMinimalBlock_nonempty x hp)
  exact Classical.choice (by
    rcases D.degree_sixteen_alternatives hX with h2 | h4 | h8
    · exact ⟨.pair x D h2.1 h2.2⟩
    · exact ⟨.four x D h4.1 h4.2⟩
    · exact ⟨.eight x D h8.1 h8.2⟩)

end SymmetricSubgroupAsymptotics

end
