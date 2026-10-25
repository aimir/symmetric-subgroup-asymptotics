import SymmetricSubgroupAsymptotics.SmallFibreNonaffinePerIndexClassResidual
import SymmetricSubgroupAsymptotics.SmallFibreScaledClassEnvelopeNumerics

/-! Scaled packets close the SAME original small-fibre action, not only
its multiple/power/far forms. The actual per-index class quantity is
retained in the short one-factor branch. A second consumer derives it
from the proved logarithmic-or-power order packet above index2048. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.SmallFibreScaledClassPacketGap
open PrimitiveSocleRawStructure OriginalBlockClassBound

variable {A Ω X : Type} [Group A] [MulAction A Ω] [MulAction A X]
    [Finite A] [Finite Ω] [Finite X] [FaithfulSMul A Ω]

theorem subnormal_class_cube_gap_of_scaled_class_packet
    (π : Ω → X) (hπ : ∀ (g : A) (ω : Ω), π (g • ω)=g • π ω)
    (c : ℕ) (hc : c=2 ∨ c=3)
    (hsize : ∀ x, Nat.card (originalBlockFibre π x)=c)
    (E : NonaffineData (Top (A := A) (X := X)) X)
    (hscaled : ∀ K : Subgroup E.Simple, K ≠ ⊤ →
      25*(Nat.card (ConjClasses E.Simple)*Nat.card (Outer E.Simple))^3 ≤ 3^K.index)
    (hsquare : ∀ ell : ℕ, LeastProperIndex E.Simple ell → ell^2 < Nat.card E.Simple)
    (H : Subgroup A) (hH : H.IsSubnormal) :
    Nat.card (ConjClasses H)^3 ≤ 5^(Nat.card Ω-2) := by
  let B := Nat.card (ConjClasses E.Simple)*Nat.card (Outer E.Simple)
  have hbudget : ∀ K : Subgroup E.Simple, K ≠ ⊤ → B^3 ≤ 5^(K.index+1) := by
    intro K hK
    calc
      B^3 ≤ 25*B^3 := Nat.le_mul_of_pos_left _ (by decide : 0 < (25:ℕ))
      _ ≤ 3^K.index := hscaled K hK
      _ ≤ 5^K.index := Nat.pow_le_pow_left (by decide) _
      _ ≤ 5^(K.index+1) := Nat.pow_le_pow_right (by decide) (by omega)
  rcases SmallFibreNonaffinePerIndexClassResidual.subnormal_gap_or_least_short_index
      π hπ c hc hsize E hbudget hsquare H hH with
      hgap | ⟨hk,ell,hell,K,hK,hdegree,hlo,hhi⟩
  · exact hgap
  · have hn : 5 ≤ Nat.card X := by
      have he := nonabelianSimple_proper_index_five_le
        (fun h => E.noncommutative (isMulCommutative_iff.mpr h)) K hK
      rw [hdegree]
      exact he
    have hB : 25*B^3 ≤ 3^Nat.card X := by rw [hdegree]; exact hscaled K hK
    have htop : ∀ L : Subgroup (Top (A := A) (X := X)), L.IsSubnormal →
        Nat.card (ConjClasses L) ≤ B := by
      intro L hL
      simpa only [hk,pow_one,Nat.factorial_one,mul_one] using
        E.subnormal_class_card_le_outer_wreath L hL
    have hlocal : ∀ x (L : Subgroup (Equiv.Perm (originalBlockFibre π x))),
        Nat.card (ConjClasses L) ≤ c := by
      rcases hc with rfl | rfl
      · exact fun x L => SmallPermutationClassBudgets.subgroup_class_card_le_two (hsize x).le L
      · exact fun x L => SmallPermutationClassBudgets.subgroup_class_card_le_three (hsize x).le L
    have hbound := SubnormalSmallFibreTopClassBound.subnormal_class_card_le_power_mul_top_budget
      π hπ c hlocal B htop H hH
    have hnum : (c^Nat.card X*B)^3 ≤ 5^(c*Nat.card X-2) := by
      rcases hc with rfl | rfl
      · exact SmallFibreScaledClassEnvelopeNumerics.binary_gap_of_scaled_cube
          (Nat.card X) B (by omega) hB
      · exact SmallFibreScaledClassEnvelopeNumerics.ternary_gap_of_scaled_cube
          (Nat.card X) B (by omega) hB
    have hcard := GaronziMarotiLargeBlockReduction.card_eq_blocks_mul_fibre π c hsize
    have h := (Nat.pow_le_pow_left hbound 3).trans hnum
    simpa only [hcard,Nat.mul_comm (Nat.card X) c] using h

theorem subnormal_class_cube_gap_of_log_or_power_order
    (π : Ω → X) (hπ : ∀ (g : A) (ω : Ω), π (g • ω)=g • π ω)
    (c : ℕ) (hc : c=2 ∨ c=3)
    (hsize : ∀ x, Nat.card (originalBlockFibre π x)=c)
    (E : NonaffineData (Top (A := A) (X := X)) X)
    (hindex : ∀ K : Subgroup E.Simple, K ≠ ⊤ → 2048 ≤ K.index)
    (horder : ∀ K : Subgroup E.Simple, K ≠ ⊤ →
      Nat.card E.Simple*Nat.card (Outer E.Simple) ≤ K.index^(4*Nat.log 2 K.index+23) ∨
      Nat.card E.Simple*Nat.card (Outer E.Simple) ≤ K.index^66)
    (hsquare : ∀ ell : ℕ, LeastProperIndex E.Simple ell → ell^2 < Nat.card E.Simple)
    (H : Subgroup A) (hH : H.IsSubnormal) :
    Nat.card (ConjClasses H)^3 ≤ 5^(Nat.card Ω-2) := by
  apply subnormal_class_cube_gap_of_scaled_class_packet π hπ c hc hsize E ?_ hsquare H hH
  intro K hK
  have hi := hindex K hK
  have hclass : Nat.card (ConjClasses E.Simple) ≤ Nat.card E.Simple :=
    Nat.card_le_card_of_surjective ConjClasses.mk ConjClasses.mk_surjective
  have hcube : (Nat.card (ConjClasses E.Simple)*Nat.card (Outer E.Simple))^3 ≤
      (Nat.card E.Simple*Nat.card (Outer E.Simple))^3 :=
    Nat.pow_le_pow_left (Nat.mul_le_mul_right _ hclass) 3
  rcases horder K hK with hlog | hpower
  · exact ((Nat.mul_le_mul_left 25 hcube).trans
      (Nat.mul_le_mul_left 25 (Nat.pow_le_pow_left hlog 3))).trans
        (SmallFibreScaledClassEnvelopeNumerics.scaled_log_power_le_three_power K.index hi)
  · have hp : (K.index^66)^3=K.index^198 := by rw [←pow_mul]
    have hh := (Nat.mul_le_mul_left 25 hcube).trans
      (Nat.mul_le_mul_left 25 (Nat.pow_le_pow_left hpower 3))
    rw [hp] at hh
    exact hh.trans (LargeIndexPowerThreeEnvelopeNumerics.scaled_power_le_three_power K.index hi)

end SymmetricSubgroupAsymptotics.SmallFibreScaledClassPacketGap
