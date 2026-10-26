import SymmetricSubgroupAsymptotics.SmallFibreReeFFourFieldEightClassResidual
import SymmetricSubgroupAsymptotics.NonabelianSimpleClassOrderHalf

/-! The actual nonabelian-simple half-class saving pays the entire
ternary q8 small-fibre branch from its original proper index109.
The original action, subnormal source and all socle factors remain.
No exact group order, action census or index-gap premise is used. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.SmallFibreReeFFourFieldEightTernaryClassGap
open PrimitiveSocleRawStructure OriginalBlockClassBound CFSGReduction

theorem ternary_numerical_gap (n : ℕ) (hn : 109≤n) :
    (3^n*(3*2^77))^3≤5^(3*n-2) := by
  induction n,hn using Nat.le_induction with
  | base => decide +kernel
  | succ n hn ih =>
    calc
      _=27*(3^n*(3*2^77))^3 := by rw [pow_succ]; ring
      _≤27*5^(3*n-2) := Nat.mul_le_mul_left _ ih
      _≤125*5^(3*n-2) := Nat.mul_le_mul_right _ (by decide : (27:ℕ)≤125)
      _=5^(3*(n+1)-2) := by
        rw [show 3*(n+1)-2=(3*n-2)+3 by omega,pow_add]
        ring

theorem subnormal_class_cube_gap
    {A Ω X : Type} [Group A] [MulAction A Ω] [MulAction A X]
    [Finite A] [Finite Ω] [Finite X] [FaithfulSMul A Ω]
    (π : Ω → X) (hπ : ∀ (g:A) (ω:Ω),π (g•ω)=g•π ω)
    (hsize : ∀ x,Nat.card (originalBlockFibre π x)=3)
    (E : NonaffineData (Top (A:=A) (X:=X)) X)
    (e : E.Simple≃*CFSG.Models.ReeF4 1)
    (H : Subgroup A) (hH : H.IsSubnormal) :
    Nat.card (ConjClasses H)^3≤5^(Nat.card Ω-2) := by
  rcases SmallFibreReeFFourFieldEightClassResidual.subnormal_gap_or_same_short_index
      π hπ 3 (Or.inr rfl) hsize E e H hH with hgap|⟨hk,K,hK,hdegree,hlo,_⟩
  · exact hgap
  · have hn : 109≤Nat.card X := by rw [hdegree]; exact hlo
    have horder : Nat.card E.Simple≤2*(2^77) := by
      rw [Nat.card_congr e.toEquiv]
      exact (CFSGReeFFourWeightedFixedOrderUpper.original_ree_order_le 1).trans_eq
        (by decide : (8:ℕ)^26=2*(2^77))
    have hclass : Nat.card (ConjClasses E.Simple)≤2^77 := by
      have hh := NonabelianSimpleClassOrderHalf.twice_class_card_le_order E.noncommutative
      omega
    have houter : Nat.card (Outer E.Simple)≤3 := by
      rw [outer_card_congr e]
      exact CFSGReeFFourOriginalOuterBound.outer_card_le 1 (by omega)
    have hB : Nat.card (ConjClasses E.Simple)*Nat.card (Outer E.Simple)≤3*2^77 :=
      (Nat.mul_le_mul hclass houter).trans_eq (Nat.mul_comm _ _)
    have htop : ∀ L : Subgroup (Top (A:=A) (X:=X)),L.IsSubnormal →
        Nat.card (ConjClasses L)≤3*2^77 := by
      intro L hL
      exact (E.subnormal_class_card_le_of_factor_one hk L hL).trans hB
    have hlocal : ∀ x (L : Subgroup (Equiv.Perm (originalBlockFibre π x))),
        Nat.card (ConjClasses L)≤3 :=
      fun x L => SmallPermutationClassBudgets.subgroup_class_card_le_three (hsize x).le L
    have hb := SubnormalSmallFibreTopClassBound.subnormal_class_card_le_power_mul_top_budget
      π hπ 3 hlocal (3*2^77) htop H hH
    have hh := (Nat.pow_le_pow_left hb 3).trans (ternary_numerical_gap (Nat.card X) hn)
    have hc := GaronziMarotiLargeBlockReduction.card_eq_blocks_mul_fibre π 3 hsize
    simpa only [hc,Nat.mul_comm (Nat.card X) 3] using hh

end SymmetricSubgroupAsymptotics.SmallFibreReeFFourFieldEightTernaryClassGap
