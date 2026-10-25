import SymmetricSubgroupAsymptotics.FourPointSubnormalClassSaving
import SymmetricSubgroupAsymptotics.ActualBlockProperClassDichotomy

/-! Strict subnormal class budgets transported through an actual
component equivalence to S4. The original component and its correlated
block kernel are retained throughout. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.SymmetricFourComponentClassBudgets

theorem subgroup_class_card_le_five
    {C : Type} [Group C] [Finite C] (e : C ≃* Equiv.Perm (Fin 4)) (L : Subgroup C) :
    Nat.card (ConjClasses L) ≤ 5 := by
  have h := FourPointPermutationClassBound.subgroup_class_card_le_five
    (L.map e.toMonoidHom)
  exact (conjugacyClass_card_congr (e.subgroupMap L)).le.trans h

theorem proper_subnormal_class_card_le_four
    {C : Type} [Group C] [Finite C] (e : C ≃* Equiv.Perm (Fin 4))
    (L : Subgroup C) (hL : L.IsSubnormal) (hne : L ≠ ⊤) :
    Nat.card (ConjClasses L) ≤ 4 := by
  have hm : (L.map e.toMonoidHom).IsSubnormal := hL.map e.surjective
  have hmt : L.map e.toMonoidHom ≠ ⊤ := by
    intro ht
    apply hne
    apply top_unique
    intro x _
    apply (Subgroup.mem_map_iff_mem (f := e.toMonoidHom) (K := L) (x := x)
      (show Function.Injective e.toMonoidHom from e.injective)).mp
    rw [ht]
    trivial
  have h := FourPointSubnormalClassSaving.proper_subnormal_class_card_le_four
    (L.map e.toMonoidHom) hm hmt
  exact (conjugacyClass_card_congr (e.subgroupMap L)).le.trans h

theorem class_saving_or_full_wreath
    {A Ω X : Type} [Group A] [MulAction A Ω] [MulAction A X]
    [MulAction.IsPretransitive A X] [FaithfulSMul A Ω]
    [Finite A] [Finite Ω] [Finite X]
    (b : Ω → X) (hb : ∀ (a : A) (ω : Ω), b (a • ω) = a • b ω) (x0 : X)
    (e : originalBlockComponent b hb x0 ≃*
      Equiv.Perm (Fin 4)) :
    Nat.card (ConjClasses A) ≤
      (4 * 5 ^ (Nat.card X - 1)) *
        Nat.card (ConjClasses (OriginalBlockClassBound.Top (A := A) (X := X))) ∨
      Nonempty (A ≃* PermutationalWreathProduct
        (originalBlockComponent b hb x0)
        (OriginalBlockClassBound.Top (A := A) (X := X)) X) := by
  exact ActualBlockProperClassDichotomy.class_saving_or_full_wreath b hb x0 5
    (fun L _ => subgroup_class_card_le_five e L)
    (fun L hL hne => proper_subnormal_class_card_le_four e L hL hne)

end SymmetricSubgroupAsymptotics.SymmetricFourComponentClassBudgets
