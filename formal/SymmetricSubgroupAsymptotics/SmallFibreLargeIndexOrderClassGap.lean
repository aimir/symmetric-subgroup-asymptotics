import SymmetricSubgroupAsymptotics.SmallFibreLargeIndexOrderClassResidual
import SymmetricSubgroupAsymptotics.LargeIndexPowerThreeEnvelopeNumerics

/-! The actual order-at-index packet closes every multiplicity and both
degree forms for small fibres, once proper indices are at least2048.
The previous actual residual pays multiple/power/far forms; its remaining
one-factor subgroup supplies the SAME index for the sharper dyadic
envelope. No action row, desired class-capacity input or full-base
comparison is used. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.SmallFibreLargeIndexOrderClassGap
open PrimitiveSocleRawStructure OriginalBlockClassBound

variable {A Ω X : Type} [Group A] [MulAction A Ω] [MulAction A X]
    [Finite A] [Finite Ω] [Finite X] [FaithfulSMul A Ω]

theorem subnormal_class_cube_gap_of_order_index_power
    (π : Ω → X) (hπ : ∀ (g : A) (ω : Ω), π (g • ω)=g • π ω)
    (c : ℕ) (hc : c=2 ∨ c=3)
    (hsize : ∀ x, Nat.card (originalBlockFibre π x)=c)
    (E : NonaffineData (Top (A := A) (X := X)) X)
    (hindex : ∀ K : Subgroup E.Simple, K ≠ ⊤ → 2048 ≤ K.index)
    (horder : ∀ K : Subgroup E.Simple, K ≠ ⊤ →
      Nat.card E.Simple*Nat.card (Outer E.Simple) ≤ K.index^66)
    (hsquare : ∀ ell : ℕ, LeastProperIndex E.Simple ell → ell^2 < Nat.card E.Simple)
    (H : Subgroup A) (hH : H.IsSubnormal) :
    Nat.card (ConjClasses H)^3 ≤ 5^(Nat.card Ω-2) := by
  rcases SmallFibreLargeIndexOrderClassResidual.subnormal_gap_or_least_short_index_of_order_index_power
      π hπ c hc hsize E
      (fun K hK => (by decide : 1024 ≤ 2048).trans (hindex K hK))
      horder hsquare H hH with hgap | ⟨hk,ell,hell,K,hK,hdegree,hlo,hhi⟩
  · exact hgap
  · let B := Nat.card E.Simple*Nat.card (Outer E.Simple)
    have hn : 2048 ≤ Nat.card X := by rw [hdegree]; exact hindex K hK
    have hB : B ≤ Nat.card X^66 := by rw [hdegree]; exact horder K hK
    have hclass : Nat.card (ConjClasses E.Simple) ≤ Nat.card E.Simple :=
      Nat.card_le_card_of_surjective ConjClasses.mk ConjClasses.mk_surjective
    have htop : ∀ L : Subgroup (Top (A := A) (X := X)), L.IsSubnormal →
        Nat.card (ConjClasses L) ≤ B := by
      intro L hL
      have hw := E.subnormal_class_card_le_outer_wreath L hL
      have hw' : Nat.card (ConjClasses L) ≤
          Nat.card (ConjClasses E.Simple)*Nat.card (Outer E.Simple) := by
        simpa only [hk,pow_one,Nat.factorial_one,mul_one] using hw
      exact hw'.trans (Nat.mul_le_mul_right _ hclass)
    have hlocal : ∀ x (L : Subgroup (Equiv.Perm (originalBlockFibre π x))),
        Nat.card (ConjClasses L) ≤ c := by
      rcases hc with rfl | rfl
      · exact fun x L => SmallPermutationClassBudgets.subgroup_class_card_le_two (hsize x).le L
      · exact fun x L => SmallPermutationClassBudgets.subgroup_class_card_le_three (hsize x).le L
    have hbound := SubnormalSmallFibreTopClassBound.subnormal_class_card_le_power_mul_top_budget
      π hπ c hlocal B htop H hH
    have hnum : (c^Nat.card X*B)^3 ≤ 5^(c*Nat.card X-2) := by
      rcases hc with rfl | rfl
      · exact LargeIndexPowerThreeEnvelopeNumerics.binary_product_cube_gap (Nat.card X) B hn hB
      · exact LargeIndexPowerThreeEnvelopeNumerics.ternary_product_cube_gap (Nat.card X) B hn hB
    have hcard := GaronziMarotiLargeBlockReduction.card_eq_blocks_mul_fibre π c hsize
    have h := (Nat.pow_le_pow_left hbound 3).trans hnum
    simpa only [hcard,Nat.mul_comm (Nat.card X) c] using h

end SymmetricSubgroupAsymptotics.SmallFibreLargeIndexOrderClassGap
