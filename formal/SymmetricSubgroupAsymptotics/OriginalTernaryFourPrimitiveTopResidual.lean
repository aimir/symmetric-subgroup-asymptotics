import SymmetricSubgroupAsymptotics.PrimitiveFourPointComponentClassData
import SymmetricSubgroupAsymptotics.PermutationBlockClassReduction
import SymmetricSubgroupAsymptotics.SmallPermutationClassBudgets
import SymmetricSubgroupAsymptotics.GaronziMarotiLargeBlockReduction
import SymmetricSubgroupAsymptotics.OriginalMinimalBlockComponentTransport

/-! The cap-four branch of an actual primitive four-point top is paid
by the original coordinate recurrence. The remaining alternative is an
actual equivalence of that same top with S4; it is not declared closed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical BigOperators
namespace SymmetricSubgroupAsymptotics.OriginalTernaryFourPrimitiveTopResidual
open OriginalBlockClassBound

theorem class_cube_le_or_symmetric_top
    {A Ω X : Type} [Group A] [MulAction A Ω] [MulAction A X]
    [Finite A] [Finite Ω] [Finite X] [FaithfulSMul A Ω]
    (π : Ω → X) (hπ : ∀ (g : A) (ω : Ω),π (g • ω)=g • π ω)
    (hsize : ∀ x,Nat.card (originalBlockFibre π x)=3)
    (hn : Nat.card X=4)
    (hprimitive : MulAction.IsPreprimitive (Top (A:=A) (X:=X)) X) :
    Nat.card (ConjClasses A)^3≤5^(Nat.card Ω-1) ∨
      Nonempty (Top (A:=A) (X:=X) ≃* Equiv.Perm (Fin 4)) := by
  rcases PrimitiveFourPointComponentClassData.all_subgroup_cap_or_symmetric
      X (Top (A:=A) (X:=X)) hprimitive hn with hcap|he
  · left
    letI : Fintype X := Fintype.ofFinite X
    have ht : Nat.card (ConjClasses (Top (A:=A) (X:=X)))≤4 := by
      have h := hcap (⊤ : Subgroup (Top (A:=A) (X:=X)))
      rw [conjugacyClass_card_congr (Subgroup.topEquiv :
        (⊤ : Subgroup (Top (A:=A) (X:=X))) ≃* Top (A:=A) (X:=X))] at h
      exact h
    have hrec := PermutationBlockClassReduction.class_card_le_product_mul_top
      π hπ (fun _ => 3)
      (fun x L => SmallPermutationClassBudgets.subgroup_class_card_le_three (hsize x).le L)
    have hc : Nat.card (ConjClasses A)≤324 := by
      have hr : Nat.card (ConjClasses A)≤3^Nat.card X*
          Nat.card (ConjClasses (Top (A:=A) (X:=X))) := by
        simpa only [Finset.prod_const,Finset.card_univ,Nat.card_eq_fintype_card] using hrec
      rw [hn] at hr
      nlinarith
    have hd : Nat.card Ω=12 := by
      have h := GaronziMarotiLargeBlockReduction.card_eq_blocks_mul_fibre π 3 hsize
      simpa only [hn] using h
    calc
      _≤324^3 := Nat.pow_le_pow_left hc 3
      _≤5^(Nat.card Ω-1) := by rw [hd]; decide
  · exact Or.inr he

end SymmetricSubgroupAsymptotics.OriginalTernaryFourPrimitiveTopResidual
