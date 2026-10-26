import SymmetricSubgroupAsymptotics.AffineTopLowDimensionSmallFibreNumerics
import SymmetricSubgroupAsymptotics.AffinePrimePowerOrderBound
import SymmetricSubgroupAsymptotics.SubnormalSmallFibreTopClassBound
import SymmetricSubgroupAsymptotics.GaronziMarotiLargeBlockReduction

/-! Actual translation-prime dimension bounds pay the original binary
and ternary fibres uniformly. The affine order and projected subgroup
are those of the same profile; no class capacity is supplied. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.AffineTopLowDimensionSmallFibreClassBound
open OriginalBlockClassBound

variable {A Ω X : Type} [Group A] [MulAction A Ω] [MulAction A X]
    [Finite A] [Finite Ω] [Finite X] [FaithfulSMul A Ω]

theorem subnormal_class_cube_le_of_affine_top_dimension
    (π : Ω → X) (hπ : ∀ (g : A) (ω : Ω), π (g • ω)=g • π ω)
    (c : ℕ) (hc : c=2 ∨ c=3)
    (hsize : ∀ x, Nat.card (originalBlockFibre π x)=c)
    (P : PrimitiveAffineProfile (Top (A:=A) (X:=X)) X)
    (hd : (49 ≤ Nat.card X ∧ Nat.log P.p (Nat.card X) ≤ 3) ∨
      (64 ≤ Nat.card X ∧ Nat.log P.p (Nat.card X) ≤ 4))
    (H : Subgroup A) (hH : H.IsSubnormal) :
    Nat.card (ConjClasses H)^3 ≤ 5^(Nat.card Ω-1) := by
  have hn : 49 ≤ Nat.card X := by rcases hd with h|h <;> omega
  letI : Nonempty X := Finite.card_pos_iff.mp (by omega)
  let x₀ : X := Classical.arbitrary X
  have ho : Nat.card (Top (A:=A) (X:=X)) ≤
      Nat.card X^(Nat.log P.p (Nat.card X)+1) := by
    calc
      _ ≤ Nat.card X*Nat.card X^Nat.log P.p (Nat.card X) :=
        AffinePrimePowerOrderBound.card_le_degree_mul_prime_log_power P x₀
      _ = _ := by rw [pow_succ,Nat.mul_comm]
  have ht : ∀ L : Subgroup (Top (A:=A) (X:=X)), L.IsSubnormal →
      Nat.card (ConjClasses L) ≤ Nat.card (Top (A:=A) (X:=X)) := by
    intro L _
    exact (Nat.card_le_card_of_surjective ConjClasses.mk ConjClasses.mk_surjective).trans
      (Nat.card_le_card_of_injective L.subtype Subtype.val_injective)
  rcases hc with rfl | rfl
  · have hlocal : ∀ x (L : Subgroup (Equiv.Perm (originalBlockFibre π x))),
        Nat.card (ConjClasses L) ≤ 2 :=
      fun x L => SmallPermutationClassBudgets.subgroup_class_card_le_two (hsize x).le L
    have hb := SubnormalSmallFibreTopClassBound.subnormal_class_card_le_power_mul_top_budget
      π hπ 2 hlocal (Nat.card (Top (A:=A) (X:=X))) ht H hH
    have hnum : (2^Nat.card X*Nat.card (Top (A:=A) (X:=X)))^3 ≤
        5^(2*Nat.card X-1) := by
      rcases hd with ⟨hn,hd⟩ | ⟨hn,hd⟩
      · exact AffineTopLowDimensionSmallFibreNumerics.binary_fourth_order _ _ hn
          (ho.trans (Nat.pow_le_pow_right (by omega) (by omega)))
      · exact AffineTopLowDimensionSmallFibreNumerics.binary_fifth_order _ _ hn
          (ho.trans (Nat.pow_le_pow_right (by omega) (by omega)))
    have hh := (Nat.pow_le_pow_left hb 3).trans hnum
    have hcard := GaronziMarotiLargeBlockReduction.card_eq_blocks_mul_fibre π 2 hsize
    simpa only [hcard,Nat.mul_comm (Nat.card X) 2] using hh
  · have hlocal : ∀ x (L : Subgroup (Equiv.Perm (originalBlockFibre π x))),
        Nat.card (ConjClasses L) ≤ 3 :=
      fun x L => SmallPermutationClassBudgets.subgroup_class_card_le_three (hsize x).le L
    have hb := SubnormalSmallFibreTopClassBound.subnormal_class_card_le_power_mul_top_budget
      π hπ 3 hlocal (Nat.card (Top (A:=A) (X:=X))) ht H hH
    have hnum : (3^Nat.card X*Nat.card (Top (A:=A) (X:=X)))^3 ≤
        5^(3*Nat.card X-1) := by
      rcases hd with ⟨hn,hd⟩ | ⟨hn,hd⟩
      · exact AffineTopLowDimensionSmallFibreNumerics.ternary_fourth_order _ _ hn
          (ho.trans (Nat.pow_le_pow_right (by omega) (by omega)))
      · exact AffineTopLowDimensionSmallFibreNumerics.ternary_fifth_order _ _ hn
          (ho.trans (Nat.pow_le_pow_right (by omega) (by omega)))
    have hh := (Nat.pow_le_pow_left hb 3).trans hnum
    have hcard := GaronziMarotiLargeBlockReduction.card_eq_blocks_mul_fibre π 3 hsize
    simpa only [hcard,Nat.mul_comm (Nat.card X) 3] using hh

end SymmetricSubgroupAsymptotics.AffineTopLowDimensionSmallFibreClassBound
