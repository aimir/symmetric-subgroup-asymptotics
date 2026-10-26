import SymmetricSubgroupAsymptotics.SmallFibreTypeARankThreeBinaryClassResidual

/-! The SAME original binary/ternary small-fibre action over PSL4(2)
pays the ordinary GM exponent |Omega|-1 in all factor/degree forms.
The stronger |Omega|-2 ternary degree8 seam is retained by the imported
residual theorem; its plain28 top ceiling already pays |Omega|-1.
No strengthened profile or supplied local class budget is asserted. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.SmallFibreTypeARankThreeBinaryOrdinaryClassGap
open PrimitiveSocleRawStructure OriginalBlockClassBound CFSGReduction

variable {A Ω X : Type} [Group A] [MulAction A Ω] [MulAction A X]
    [Finite A] [Finite Ω] [Finite X] [FaithfulSMul A Ω]

theorem subnormal_class_cube_gap_at_original_degree
    (π : Ω→X) (hπ : ∀ (g:A) (ω:Ω),π (g•ω)=g•π ω)
    (c : ℕ) (hc : c=2 ∨ c=3)
    (hsize : ∀ x,Nat.card (originalBlockFibre π x)=c)
    (E : NonaffineData (Top (A:=A) (X:=X)) X)
    (q : CFSG.PrimePower) (hq : q.order=2) (e : E.Simple≃*CFSG.Models.A 3 q)
    (H : Subgroup A) (hH : H.IsSubnormal) :
    Nat.card (ConjClasses H)^3≤5^(Nat.card Ω-1) := by
  rcases SmallFibreTypeARankThreeBinaryClassResidual.subnormal_gap_or_ternary_eight
      π hπ c hc hsize E q hq e H hH with hgap | ⟨hc3,hk,K,hK,hdegree,hidx⟩
  · exact hgap.trans (Nat.pow_le_pow_right (by decide) (by omega))
  · letI : IsSimpleGroup (CFSG.Models.A 3 q) := e.symm.isSimpleGroup
    letI : Finite (CFSG.Models.A 3 q) := Finite.of_equiv E.Simple e.toEquiv
    have hclasses : Nat.card (ConjClasses E.Simple)=Nat.card (ConjClasses (CFSG.Models.A 3 q)) := by
      apply Nat.le_antisymm
      · exact Nat.card_le_card_of_surjective (ConjClasses.map e.symm.toMonoidHom)
          (ConjClasses.map_surjective e.symm.surjective)
      · exact Nat.card_le_card_of_surjective (ConjClasses.map e.toMonoidHom)
          (ConjClasses.map_surjective e.surjective)
    have hcomponent : Nat.card (ConjClasses E.Simple)*Nat.card (Outer E.Simple)≤28 := by
      rw [hclasses,outer_card_congr e]
      exact CFSGTypeARankThreeBinaryClassPacket.component_class_card_le_twentyEight q hq
    have htop : ∀ L : Subgroup (Top (A:=A) (X:=X)), L.IsSubnormal →
        Nat.card (ConjClasses L)≤28 := by
      intro L hL
      have hh : Nat.card (ConjClasses L)≤
          Nat.card (ConjClasses E.Simple)*Nat.card (Outer E.Simple) := by
        simpa only [hk,pow_one,Nat.factorial_one,mul_one] using
          E.subnormal_class_card_le_outer_wreath L hL
      exact hh.trans hcomponent
    have hsize3 : ∀ x,Nat.card (originalBlockFibre π x)=3 := fun x=>(hsize x).trans hc3
    have hlocal : ∀ x (L : Subgroup (Equiv.Perm (originalBlockFibre π x))),
        Nat.card (ConjClasses L)≤3 :=
      fun x L => SmallPermutationClassBudgets.subgroup_class_card_le_three (hsize3 x).le L
    have hbound := SubnormalSmallFibreTopClassBound.subnormal_class_card_le_power_mul_top_budget
      π hπ 3 hlocal 28 htop H hH
    have hn : Nat.card X=8 := hdegree.trans hidx
    have hnum : (3^Nat.card X*28)^3≤5^(3*Nat.card X-1) := by
      rw [hn]
      decide +kernel
    have hcard := GaronziMarotiLargeBlockReduction.card_eq_blocks_mul_fibre π 3 hsize3
    have hh := (Nat.pow_le_pow_left hbound 3).trans hnum
    simpa only [hcard,Nat.mul_comm (Nat.card X) 3] using hh

end SymmetricSubgroupAsymptotics.SmallFibreTypeARankThreeBinaryOrdinaryClassGap
