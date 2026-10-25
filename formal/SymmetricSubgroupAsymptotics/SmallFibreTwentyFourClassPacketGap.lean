import SymmetricSubgroupAsymptotics.SmallFibreNonaffinePerIndexClassResidual
import SymmetricSubgroupAsymptotics.SmallFibreTwentyFourClassEnvelopeNumerics

/-! The24-reserve packet pays the SAME original small-fibre action,
arbitrary actual subnormal subgroup, full socle factor count and degree
forms. All previous25-reserve endpoints remain intact. No small-model
class bound, splitting or numerical packet is supplied as a new input. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.SmallFibreTwentyFourClassPacketGap
open PrimitiveSocleRawStructure OriginalBlockClassBound

variable {A Ω X : Type} [Group A] [MulAction A Ω] [MulAction A X]
    [Finite A] [Finite Ω] [Finite X] [FaithfulSMul A Ω]

theorem subnormal_class_cube_gap_of_scaled_class_packet
    (π : Ω → X) (hπ : ∀ (g : A) (ω : Ω), π (g • ω)=g • π ω)
    (c : ℕ) (hc : c=2 ∨ c=3)
    (hsize : ∀ x, Nat.card (originalBlockFibre π x)=c)
    (E : NonaffineData (Top (A := A) (X := X)) X)
    (hscaled : ∀ K : Subgroup E.Simple, K≠⊤ →
      24*(Nat.card (ConjClasses E.Simple)*Nat.card (Outer E.Simple))^3≤3^K.index)
    (hsquare : ∀ ell : ℕ, LeastProperIndex E.Simple ell → ell^2<Nat.card E.Simple)
    (H : Subgroup A) (hH : H.IsSubnormal) :
    Nat.card (ConjClasses H)^3≤5^(Nat.card Ω-2) := by
  let B := Nat.card (ConjClasses E.Simple)*Nat.card (Outer E.Simple)
  have hbudget : ∀ K : Subgroup E.Simple, K≠⊤ → B^3≤5^(K.index+1) := by
    intro K hK
    calc
      B^3≤24*B^3 := Nat.le_mul_of_pos_left _ (by decide : 0<(24:ℕ))
      _≤3^K.index := hscaled K hK
      _≤5^K.index := Nat.pow_le_pow_left (by decide) _
      _≤5^(K.index+1) := Nat.pow_le_pow_right (by decide) (by omega)
  rcases SmallFibreNonaffinePerIndexClassResidual.subnormal_gap_or_least_short_index
      π hπ c hc hsize E hbudget hsquare H hH with
      hgap | ⟨hk,ell,hell,K,hK,hdegree,hlo,hhi⟩
  · exact hgap
  · have hn : 5≤Nat.card X := by
      have he := nonabelianSimple_proper_index_five_le
        (fun h => E.noncommutative (isMulCommutative_iff.mpr h)) K hK
      rw [hdegree]
      exact he
    have hB : 24*B^3≤3^Nat.card X := by rw [hdegree]; exact hscaled K hK
    have htop : ∀ L : Subgroup (Top (A := A) (X := X)), L.IsSubnormal →
        Nat.card (ConjClasses L)≤B := by
      intro L hL
      simpa only [hk,pow_one,Nat.factorial_one,mul_one] using
        E.subnormal_class_card_le_outer_wreath L hL
    have hlocal : ∀ x (L : Subgroup (Equiv.Perm (originalBlockFibre π x))),
        Nat.card (ConjClasses L)≤c := by
      rcases hc with rfl | rfl
      · exact fun x L => SmallPermutationClassBudgets.subgroup_class_card_le_two (hsize x).le L
      · exact fun x L => SmallPermutationClassBudgets.subgroup_class_card_le_three (hsize x).le L
    have hbound := SubnormalSmallFibreTopClassBound.subnormal_class_card_le_power_mul_top_budget
      π hπ c hlocal B htop H hH
    have hnum : (c^Nat.card X*B)^3≤5^(c*Nat.card X-2) := by
      rcases hc with rfl | rfl
      · exact SmallFibreTwentyFourClassEnvelopeNumerics.binary_gap_of_scaled_cube
          (Nat.card X) B (by omega) hB
      · exact SmallFibreTwentyFourClassEnvelopeNumerics.ternary_gap_of_scaled_cube
          (Nat.card X) B (by omega) hB
    have hcard := GaronziMarotiLargeBlockReduction.card_eq_blocks_mul_fibre π c hsize
    have h := (Nat.pow_le_pow_left hbound 3).trans hnum
    simpa only [hcard,Nat.mul_comm (Nat.card X) c] using h

end SymmetricSubgroupAsymptotics.SmallFibreTwentyFourClassPacketGap
