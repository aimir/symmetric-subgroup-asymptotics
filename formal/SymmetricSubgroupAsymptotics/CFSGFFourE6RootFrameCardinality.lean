import SymmetricSubgroupAsymptotics.CFSGFFourE6RootFrameTripleZero
import SymmetricSubgroupAsymptotics.CFSGFFourE6RootFrameTripleOne
import SymmetricSubgroupAsymptotics.FiniteOrthogonalFrameCardinality

/-! The complete last fibre follows from two six-positive-root certificates
and negation. The four successive orthogonal-root choices are bounded by
24, 6, 4, 2. No Weyl group is enumerated. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGFFourE6RootFrameCardinality
open CFSGFFourE6FixedRootFramePilot CFSGFFourE6RootFrameFibresPilot
open CFSGIntegerMatrixPairing FiniteOrthogonalFrameCardinality

private theorem first_root_cases : ∀x∈menu,
    x∈CFSGFFourE6RootFrameTripleZero.firstRoots ∨
    x∈CFSGFFourE6RootFrameTripleOne.firstRoots ∨
    -x∈CFSGFFourE6RootFrameTripleZero.firstRoots ∨
    -x∈CFSGFFourE6RootFrameTripleOne.firstRoots := by decide +kernel

theorem triple_orthogonal_card (x:Fin 6→ℤ) (hx:x∈menu)
    (y:Fin 6→ℤ) (hy:y∈menu) (z:Fin 6→ℤ) (hz:z∈menu)
    (hxy:integerPairing CartanMatrix.E₆ x y=0)
    (hxz:integerPairing CartanMatrix.E₆ x z=0)
    (hyz:integerPairing CartanMatrix.E₆ y z=0) :
    (menu.filter (fun w=>integerPairing CartanMatrix.E₆ x w=0∧
      integerPairing CartanMatrix.E₆ y w=0∧integerPairing CartanMatrix.E₆ z w=0)).card=2 := by
  rcases first_root_cases x hx with h|h|h|h
  · exact CFSGFFourE6RootFrameTripleZero.triple_orthogonal_card x h y hy z hz hxy hxz hyz
  · exact CFSGFFourE6RootFrameTripleOne.triple_orthogonal_card x h y hy z hz hxy hxz hyz
  · have hnxy : integerPairing CartanMatrix.E₆ (-x) y=0 := by
      simp only [map_neg,LinearMap.neg_apply,hxy,neg_zero]
    have hnxz : integerPairing CartanMatrix.E₆ (-x) z=0 := by
      simp only [map_neg,LinearMap.neg_apply,hxz,neg_zero]
    simpa only [map_neg,LinearMap.neg_apply,neg_eq_zero] using
      CFSGFFourE6RootFrameTripleZero.triple_orthogonal_card (-x) h y hy z hz hnxy hnxz hyz
  · have hnxy : integerPairing CartanMatrix.E₆ (-x) y=0 := by
      simp only [map_neg,LinearMap.neg_apply,hxy,neg_zero]
    have hnxz : integerPairing CartanMatrix.E₆ (-x) z=0 := by
      simp only [map_neg,LinearMap.neg_apply,hxz,neg_zero]
    simpa only [map_neg,LinearMap.neg_apply,neg_eq_zero] using
      CFSGFFourE6RootFrameTripleOne.triple_orthogonal_card (-x) h y hy z hz hnxy hnxz hyz

def Orth (x y:menu) : Prop := integerPairing CartanMatrix.E₆ x.val y.val=0

abbrev RootFrames := Frames Orth

theorem rootFrames_card_le : Nat.card RootFrames≤1152 := by
  apply (card_frames_le Orth 24 6 4 2 ?_ ?_ ?_ ?_).trans (by norm_num)
  · simpa only [Nat.card_eq_fintype_card,Fintype.card_coe,menu_card] using (le_refl 24)
  · intro x
    change Nat.card {y:menu // integerPairing CartanMatrix.E₆ x.val y.val=0}≤6
    rw [card_subtype_filter menu (fun y=>integerPairing CartanMatrix.E₆ x.val y=0)]
    exact le_of_eq (orthogonal_card x.val x.property)
  · intro x y
    change Nat.card {z:menu // integerPairing CartanMatrix.E₆ x.val z.val=0∧
      integerPairing CartanMatrix.E₆ y.val.val z.val=0}≤4
    rw [card_subtype_filter menu (fun z=>integerPairing CartanMatrix.E₆ x.val z=0∧
      integerPairing CartanMatrix.E₆ y.val.val z=0)]
    exact le_of_eq (pair_orthogonal_card x.val x.property y.val.val y.val.property y.property)
  · intro x y z
    change Nat.card {w:menu // integerPairing CartanMatrix.E₆ x.val w.val=0∧
      integerPairing CartanMatrix.E₆ y.val.val w.val=0∧integerPairing CartanMatrix.E₆ z.val.val w.val=0}≤2
    rw [card_subtype_filter menu (fun w=>integerPairing CartanMatrix.E₆ x.val w=0∧
      integerPairing CartanMatrix.E₆ y.val.val w=0∧integerPairing CartanMatrix.E₆ z.val.val w=0)]
    exact le_of_eq (triple_orthogonal_card x.val x.property y.val.val y.val.property
      z.val.val z.val.property y.property z.property.1 z.property.2)

end SymmetricSubgroupAsymptotics.CFSGFFourE6RootFrameCardinality
