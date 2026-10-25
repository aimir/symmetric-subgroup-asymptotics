import SymmetricSubgroupAsymptotics.CFSGClassificationTransport
import SymmetricSubgroupAsymptotics.CFSGTypeAProperIndexOrderBudget
import SymmetricSubgroupAsymptotics.CFSGUnitaryProperIndexOuterUpper
import SymmetricSubgroupAsymptotics.CFSGOrthogonalBProperIndexOrderBudget
import SymmetricSubgroupAsymptotics.CFSGSymplecticProperIndexOrderBudget
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDProperIndexOrderBudget
import SymmetricSubgroupAsymptotics.CFSGTwistedDProperIndexOrderBudget
import SymmetricSubgroupAsymptotics.CFSGGTwoProperIndexOrderBudget
import SymmetricSubgroupAsymptotics.CFSGFFourOriginalOrderUpper
import SymmetricSubgroupAsymptotics.CFSGFFourE6PermutationDegree
import SymmetricSubgroupAsymptotics.CFSGTrialityGeckProperIndexOrderBudget
import SymmetricSubgroupAsymptotics.CFSGSuzukiProperIndexOrderBudget
import SymmetricSubgroupAsymptotics.CFSGExceptionalLongChainStarIndex
import SymmetricSubgroupAsymptotics.CFSGExceptionalOriginalComponentUpper
import SymmetricSubgroupAsymptotics.CFSGTwistedE6OriginalOrderUpper
import SymmetricSubgroupAsymptotics.CFSGTwistedE6HeisenbergIndex
import SymmetricSubgroupAsymptotics.CFSGReeGTwoOriginalOrderBounds
import SymmetricSubgroupAsymptotics.CFSGReeGTwoPermutationDegree
import SymmetricSubgroupAsymptotics.CFSGReeFFourWeightedFixedOrderUpper
import SymmetricSubgroupAsymptotics.CFSGReeFFourPermutationDegree
import SymmetricSubgroupAsymptotics.CFSGReeFFourOriginalOuterBound

/-! Actual order-plus-outer bounds at every proper index, assembled for
all Lie-type models. These are the two explicit numerical alternatives
needed by the large-top small-fibre argument; neither alternative is a
class-count assumption. The remaining literal tags are alternating,
Tits and sporadic. Finiteness and simplicity are inherited from the
original source, rather than asserted for every model. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGModelComponentIndexOrderBudget
open PrimitiveSocleRawStructure CFSGReduction

def ComponentIndexOrderBudget (S : Type) [Group S] : Prop :=
  ∀ (H : Subgroup S), H ≠ ⊤ →
    Nat.card S * Nat.card (Outer S) ≤ H.index^(4*Nat.log 2 H.index+23) ∨
    Nat.card S * Nat.card (Outer S) ≤ H.index^66

def RemainingSimpleType : CFSG.Index → Prop
  | .alternating _ _ | .tits | .sporadic _ => True
  | _ => False

private theorem bounded_power (q a d m c : ℕ) (hq : 0 < q)
    (horder : c ≤ q^a) (hindex : q^d ≤ m) (hexp : a ≤ d*66) : c ≤ m^66 := by
  exact horder.trans ((Nat.pow_le_pow_right hq hexp).trans
    ((pow_mul q d 66) ▸ Nat.pow_le_pow_left hindex 66))

theorem model_budget_or_remaining (i : CFSG.Index)
    [hfinite : Finite i.Model] [hsimple : IsSimpleGroup i.Model]
    (hn : ¬ IsMulCommutative i.Model) :
    ComponentIndexOrderBudget i.Model ∨ RemainingSimpleType i := by
  cases i with
  | cyclic p hp =>
    exact (hn (by change IsMulCommutative (Multiplicative (ZMod p)); infer_instance)).elim
  | alternating n hn => exact Or.inr trivial
  | A r q hr hs =>
    letI : IsSimpleGroup (CFSG.Models.A r q) := hsimple
    letI : Finite (CFSG.Models.A r q) := hfinite
    left
    intro H hH
    exact Or.inl (CFSGTypeAProperIndexOrderBudget.typeA_order_mul_outer_le_proper_index_log_power
      r hr q H hH)
  | B r q hr =>
    letI : IsSimpleGroup (CFSG.Models.B r q) := hsimple
    letI : Finite (CFSG.Models.B r q) := hfinite
    left
    intro H hH
    exact Or.inl (CFSGOrthogonalBProperIndexOrderBudget.typeB_order_mul_outer_le_proper_index_log_power
      r hr q H hH)
  | C r q hr hs =>
    letI : IsSimpleGroup (CFSG.Models.C r q) := hsimple
    letI : Finite (CFSG.Models.C r q) := hfinite
    left
    intro H hH
    exact Or.inl (CFSGSymplecticProperIndexOrderBudget.typeC_order_mul_outer_le_proper_index_log_power
      r hr q H hH)
  | D r q hr =>
    letI : IsSimpleGroup (CFSG.Models.D r q) := hsimple
    letI : Finite (CFSG.Models.D r q) := hfinite
    left
    intro H hH
    exact Or.inl (CFSGOrthogonalDProperIndexOrderBudget.typeD_order_mul_outer_le_proper_index_log_power
      r hr q H hH)
  | twistedA r q hr hs =>
    letI : IsSimpleGroup (CFSG.Models.TwistedA r q) := hsimple
    letI : Finite (CFSG.Models.TwistedA r q) := hfinite
    left
    intro H hH
    have hb := CFSGTwistedAUnitaryCoordinates.twistedA_admissible_order_mul_outer_le_proper_index_log_power
      r hr q hs hn H hH
    exact Or.inl (hb.trans (Nat.pow_le_pow_right
      (lt_trans Nat.zero_lt_one (H.one_lt_index_of_ne_top hH))
      (Nat.add_le_add_left (by decide : 3 ≤ 23) (4*Nat.log 2 H.index))))
  | twistedD r q hr =>
    letI : IsSimpleGroup (CFSG.Models.TwistedD r q) := hsimple
    letI : Finite (CFSG.Models.TwistedD r q) := hfinite
    left
    intro H hH
    by_cases hfour : r=4
    · subst r
      exact Or.inr ((CFSGTwistedDProperIndexOrderBudget.typeTwistedD_four_order_mul_outer_le_proper_index_power
        q hn H hH).trans (Nat.pow_le_pow_right
          (lt_trans Nat.zero_lt_one (H.one_lt_index_of_ne_top hH))
          (by decide : 34 ≤ 66)))
    · exact Or.inl
        (CFSGTwistedDProperIndexOrderBudget.typeTwistedD_high_order_mul_outer_le_proper_index_log_power
          r (by omega) q hn H hH)
  | G2 q hs =>
    letI : IsSimpleGroup (CFSG.Models.G2 q) := hsimple
    letI : Finite (CFSG.Models.G2 q) := hfinite
    left
    intro H hH
    exact Or.inr (CFSGGTwoProperIndexOrderBudget.typeGTwo_order_mul_outer_le_proper_index_power
      q hs H hH)
  | F4 q =>
    letI : IsSimpleGroup (CFSG.Models.F4 q) := hsimple
    letI : Finite (CFSG.Models.F4 q) := hfinite
    left
    intro H hH
    have hi : q.order ≤ H.index := by
      simpa only [q.card_field] using
        CFSGFFourE6PermutationDegree.field_card_le_proper_index q.Field q.prime H hH
    exact Or.inr ((CFSGFFourOriginalOrderUpper.typeFFour_order_mul_outer_le q hn).trans
      (Nat.pow_le_pow_left hi 66))
  | E6 q =>
    letI : IsSimpleGroup (CFSG.Models.E6 q) := hsimple
    letI : Finite (CFSG.Models.E6 q) := hfinite
    left
    intro H hH
    exact Or.inr (bounded_power q.order 129 5 H.index _
      (Nat.pow_pos q.prime_isPrime.pos) (CFSGExceptionalOriginalComponentUpper.E6_order_mul_outer_le q hn)
      (CFSGReduction.typeE6_field_fifth_le_index q H hH) (by decide))
  | E7 q =>
    letI : IsSimpleGroup (CFSG.Models.E7 q) := hsimple
    letI : Finite (CFSG.Models.E7 q) := hfinite
    left
    intro H hH
    exact Or.inr (bounded_power q.order 192 6 H.index _
      (Nat.pow_pos q.prime_isPrime.pos) (CFSGExceptionalOriginalComponentUpper.E7_order_mul_outer_le q hn)
      (CFSGReduction.typeE7_field_sixth_le_index q H hH) (by decide))
  | E8 q =>
    letI : IsSimpleGroup (CFSG.Models.E8 q) := hsimple
    letI : Finite (CFSG.Models.E8 q) := hfinite
    left
    intro H hH
    exact Or.inr (bounded_power q.order 323 7 H.index _
      (Nat.pow_pos q.prime_isPrime.pos) (CFSGExceptionalOriginalComponentUpper.E8_order_mul_outer_le q hn)
      (CFSGReduction.typeE8_field_seventh_le_index q H hH) (by decide))
  | twistedE6 q =>
    letI : IsSimpleGroup (CFSG.Models.TwistedE6 q) := hsimple
    letI : Finite (CFSG.Models.TwistedE6 q) := hfinite
    left
    intro H hH
    have hi : q.order^10 ≤ H.index :=
      (Nat.le_mul_of_pos_left _ q.prime_isPrime.pos).trans
        (CFSGTwistedE6HeisenbergIndex.prime_mul_order_ten_le_proper_index q H hH)
    exact Or.inr (bounded_power q.order 122 10 H.index _
      (Nat.pow_pos q.prime_isPrime.pos) (CFSGTwistedE6OriginalOrderUpper.original_order_mul_outer_le q hn)
      hi (by decide))
  | trialityD4 q =>
    letI : IsSimpleGroup (CFSG.Models.TrialityD4 q) := hsimple
    letI : Finite (CFSG.Models.TrialityD4 q) := hfinite
    left
    intro H hH
    exact Or.inr (CFSGTrialityGeckProperIndexOrderBudget.original_order_mul_outer_le_proper_index_power
      q hn H hH)
  | suzuki m hm =>
    letI : IsSimpleGroup (CFSG.Models.Suzuki m) := hsimple
    letI : Finite (CFSG.Models.Suzuki m) := hfinite
    left
    intro H hH
    exact Or.inr ((CFSGSuzukiProperIndexOrderBudget.suzuki_order_mul_outer_le_proper_index_seventeen
      m hm H hH).trans (Nat.pow_le_pow_right
        (lt_trans Nat.zero_lt_one (H.one_lt_index_of_ne_top hH))
        (by decide : 17 ≤ 66)))
  | reeG2 m hm =>
    letI : IsSimpleGroup (CFSG.Models.ReeG2 m) := hsimple
    letI : Finite (CFSG.Models.ReeG2 m) := hfinite
    left
    intro H hH
    exact Or.inr (bounded_power (3^(2*m+1)) 8 1 H.index _ (by positivity)
      (CFSGReeGTwoOriginalOrderBounds.original_component_le_eighth m hm)
      (by simpa only [pow_one] using CFSGReeGTwoPermutationDegree.field_card_le_proper_index m hm H hH)
      (by decide))
  | reeF4 m hm =>
    letI : IsSimpleGroup (CFSG.Models.ReeF4 m) := hsimple
    letI : Finite (CFSG.Models.ReeF4 m) := hfinite
    left
    intro H hH
    have hout : Nat.card (Outer (CFSG.Models.ReeF4 m)) ≤ 2^(2*m+1) :=
      (CFSGReeFFourOriginalOuterBound.outer_card_le m (by omega)).trans
        (2*m+1).lt_two_pow_self.le
    have horder : Nat.card (CFSG.Models.ReeF4 m)*Nat.card (Outer (CFSG.Models.ReeF4 m)) ≤
        (2^(2*m+1))^27 :=
      (Nat.mul_le_mul (CFSGReeFFourWeightedFixedOrderUpper.original_ree_order_le m) hout).trans_eq
        (pow_succ _ 26).symm
    exact Or.inr (bounded_power (2^(2*m+1)) 27 1 H.index _ (by positivity) horder
      (by simpa only [pow_one] using CFSGReeFFourPermutationDegree.order_le_proper_index m (by omega) H hH)
      (by decide))
  | tits => exact Or.inr trivial
  | sporadic s => exact Or.inr trivial

theorem budget_of_mulEquiv {S T : Type} [Group S] [Group T]
    (e : S ≃* T) (h : ComponentIndexOrderBudget T) : ComponentIndexOrderBudget S := by
  intro H hH
  have hm : H.map e.toMonoidHom ≠ ⊤ := by
    intro he
    apply hH
    apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
    exact he.trans (Subgroup.map_top_of_surjective e.toMonoidHom e.surjective).symm
  have hb := h (H.map e.toMonoidHom) hm
  have hidx : (H.map e.toMonoidHom).index = H.index := H.index_map_equiv e
  rw [hidx] at hb
  rwa [Nat.card_congr e.toEquiv,outer_card_congr e]

theorem simple_budget_or_actual_remaining_model (hCFSG : CFSG.CFSGClassification)
    (S : Type) [Group S] [Finite S] [IsSimpleGroup S] (hn : ¬IsMulCommutative S) :
    ComponentIndexOrderBudget S ∨
      ∃ i : CFSG.Index, RemainingSimpleType i ∧ Nonempty (S ≃* i.Model) := by
  obtain ⟨i,⟨e⟩⟩ := hCFSG.classify S
  letI : Finite i.Model := Finite.of_equiv S e.toEquiv
  letI : IsSimpleGroup i.Model := e.symm.isSimpleGroup
  have hn' : ¬IsMulCommutative i.Model := fun h => hn ((isMulCommutative_congr e).mpr h)
  rcases model_budget_or_remaining i hn' with hb | hi
  · exact Or.inl (budget_of_mulEquiv e hb)
  · exact Or.inr ⟨i,hi,⟨e⟩⟩

end SymmetricSubgroupAsymptotics.CFSGModelComponentIndexOrderBudget
