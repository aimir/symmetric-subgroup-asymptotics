import SymmetricSubgroupAsymptotics.Non2PreE7SemisimpleTemplate
import SymmetricSubgroupAsymptotics.TrivialQuotientComparator

/-!
# The bounded nonsoluble primitive-affine family

The finite-target chief-series argument for one literal primitive-affine
action supplies a complete all-normal-axis envelope.  This file installs
that exact envelope in the common earlier-owner comparator without replacing
the action by an abstract ledger label.  Catalogue completeness is logically
separate: it is needed only to show that every action at the three bounded
exceptional degrees has one of these certificates.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu

/-- One literal action in the bounded nonsoluble primitive-affine family,
together with the complete fixed-target fibre bound furnished by its checked
chief-series certificate. -/
structure PreE7NsaprimActionCertificate
    (w : ℕ) (i : PreE7NonPairActionClass w) where
  width_lower : 5 ≤ w
  width_upper : w ≤ 1024
  primitive : MulAction.IsPreprimitive
    (preE7NonPairAction w i) (Fin w)
  coefficient : ℕ → ℝ
  eta : ℝ
  eta_nonneg : 0 ≤ eta
  coefficient_nonneg : ∀ b, 0 ≤ coefficient b
  complete_fibre : ∀ b (J : Subgroup (Equiv.Perm (Fin b))),
    completeQuotientWeight (R := preE7NonPairAction w i) J ≤
      coefficient b * (2 : ℝ) ^ (eta * b)
  coefficient_total_polynomial : ∃ K : ℝ, ∃ p : ℕ, 0 ≤ K ∧ ∀ b,
    fusionAxisEnvelopeTotal (preE7NonPairAction w i)
        (fun _ => coefficient b) ≤ K * (1 + (b : ℝ)) ^ p
  exponent_margin : preE7CharacterRho * w ≤
    ((evenWidth w : ℝ) - 2) / 8 - eta

namespace PreE7NsaprimActionCertificate

variable {w : ℕ} {i : PreE7NonPairActionClass w}
  (C : PreE7NsaprimActionCertificate w i)

noncomputable def polynomialConstant : ℝ :=
  Classical.choose C.coefficient_total_polynomial

noncomputable def polynomialDegree : ℕ :=
  Classical.choose (Classical.choose_spec C.coefficient_total_polynomial)

theorem polynomialConstant_nonneg : 0 ≤ C.polynomialConstant :=
  (Classical.choose_spec
    (Classical.choose_spec C.coefficient_total_polynomial)).1

theorem coefficient_total_le_polynomial (b : ℕ) :
    fusionAxisEnvelopeTotal (preE7NonPairAction w i)
        (fun _ => C.coefficient b) ≤
      C.polynomialConstant * (1 + (b : ℝ)) ^ C.polynomialDegree :=
  (Classical.choose_spec
    (Classical.choose_spec C.coefficient_total_polynomial)).2 b

def degree (_C : PreE7NsaprimActionCertificate w i) : ℕ :=
  paddedComparatorDegree preE7CharacterRho 2 w

def delta : ℝ := paddedComparatorDelta preE7CharacterRho C.eta 2 w

def cutoff : ℝ := (C.degree : ℝ) / 8 + C.delta / 2

/-- The complete pointwise NSAPRIM certificate.  The comparator is trivial:
the fixed-target chief-series theorem has already summed every literal
normal quotient of the action on the same source. -/
noncomputable def certificate :
    PreE7EarlierActionComparatorCertificate .nsaprim w i where
  R := PUnit
  groupR := inferInstance
  finiteR := inferInstance
  v := C.degree
  action := 1
  action_injective := fun _ _ _ => Subsingleton.elim _ _
  C := fun b _ => C.coefficient b
  tailCoefficient := fun _ _ => 0
  eta := C.eta
  delta := C.delta
  cutoff := C.cutoff
  alpha := C.eta + C.cutoff
  theta := 0
  alpha_eq := rfl
  coefficient_nonneg := fun b _ => C.coefficient_nonneg b
  tail_nonneg := fun _ _ => le_rfl
  broad_axis_envelope := by
    intro b N J
    rw [completeQuotientWeight_eq_one_of_subsingleton (R := PUnit) J]
    let U := preE7NonPairAction w i
    have hsurvive := fusionSurvivingEpiCount_le_groupEpimorphism_card U
      (preE7NoPairNoC3BroadActionPredicate w i b) N J
    have hsingle :
        (Nat.card (GroupEpimorphism J (U ⧸ N.1)) : ℝ) ≤
          completeQuotientWeight (R := U) J := by
      unfold completeQuotientWeight completeQuotientCount
      rw [Nat.cast_sum]
      exact Finset.single_le_sum
        (f := fun M : {M : Subgroup U // M.Normal} ↦
          (Nat.card (GroupEpimorphism J (U ⧸ M.1)) : ℝ))
        (fun M _ => Nat.cast_nonneg _) (Finset.mem_univ N)
    calc
      fusionSurvivingEpiCount U
          (preE7NoPairNoC3BroadActionPredicate w i b) N J ≤
          (Nat.card (GroupEpimorphism J (U ⧸ N.1)) : ℝ) := hsurvive
      _ ≤ completeQuotientWeight (R := U) J := hsingle
      _ ≤ C.coefficient b * (2 : ℝ) ^ (C.eta * b) := C.complete_fibre b J
      _ = (C.coefficient b * (2 : ℝ) ^ (C.eta * b)) * 1 +
          0 * (2 : ℝ) ^ ((0 : ℝ) * b) := by ring

end PreE7NsaprimActionCertificate

end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
