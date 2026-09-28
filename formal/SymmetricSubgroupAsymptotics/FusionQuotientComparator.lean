import SymmetricSubgroupAsymptotics.FusionCompleteSourceEnvelope
import SymmetricSubgroupAsymptotics.FusionEpimorphismTransport

/-!
# Literal quotient comparators for one original normal axis

An earlier owner may identify the original quotient `U/N` with one literal
quotient of a smaller comparator `R`.  The surviving maps on that axis are
then bounded by the corresponding summand of the complete quotient weight of
`R`.  No automorphism factor, quotient-type multiplicity or source change is
introduced.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics

structure FusionQuotientComparator {w : ℕ}
    (U : Subgroup (Equiv.Perm (Fin w)))
    (N : {N : Subgroup U // N.Normal})
    (R : Type*) [Group R] where
  axis : {M : Subgroup R // M.Normal}
  quotientEquiv : (U ⧸ N.1) ≃* (R ⧸ axis.1)

/-- A surviving family is a subtype of all epimorphisms to its original
quotient, and the comparator equivalence places those epimorphisms in one
literal summand of the comparator's complete quotient count. -/
theorem fusionSurvivingEpiCount_le_completeQuotientWeight_of_comparator
    {w b : ℕ}
    (U : Subgroup (Equiv.Perm (Fin w)))
    (P : Subgroup (U × Equiv.Perm (Fin b)) → Prop)
    (N : {N : Subgroup U // N.Normal})
    {R : Type*} [Group R] [Finite R]
    (C : FusionQuotientComparator U N R)
    (J : Subgroup (Equiv.Perm (Fin b))) :
    fusionSurvivingEpiCount U P N J ≤
      completeQuotientWeight (R := R) J := by
  have hsubtype :
      Nat.card {beta : GroupEpimorphism J (U ⧸ N.1) //
          P (fusionFullGoursatEncode N J beta).1} ≤
        Nat.card (GroupEpimorphism J (U ⧸ N.1)) :=
    Nat.card_le_card_of_injective Subtype.val Subtype.val_injective
  have htransport :
      Nat.card (GroupEpimorphism J (U ⧸ N.1)) =
        Nat.card (GroupEpimorphism J (R ⧸ C.axis.1)) :=
    fusionGroupEpimorphism_card_congr (MulEquiv.refl J) C.quotientEquiv
  have haxis :
      Nat.card (GroupEpimorphism J (R ⧸ C.axis.1)) ≤
        completeQuotientCount (R := R) J := by
    unfold completeQuotientCount
    exact Finset.single_le_sum
      (fun M _ => Nat.zero_le
        (Nat.card (GroupEpimorphism J (R ⧸ M.1))))
      (Finset.mem_univ C.axis)
  unfold fusionSurvivingEpiCount completeQuotientWeight
  exact_mod_cast hsubtype.trans (htransport.le.trans haxis)

/-- A whole family of literal quotient comparators supplies coefficient one
on every original normal axis. -/
theorem fusionCompleteSourceSum_le_completeQuotientWeight_mul_axisCount
    {w b : ℕ}
    (U : Subgroup (Equiv.Perm (Fin w)))
    (P : Subgroup (U × Equiv.Perm (Fin b)) → Prop)
    {R : Type*} [Group R] [Finite R]
    (C : ∀ N : {N : Subgroup U // N.Normal},
      FusionQuotientComparator U N R)
    (J : Subgroup (Equiv.Perm (Fin b))) :
    fusionCompleteSourceSum U P J ≤
      (Nat.card {N : Subgroup U // N.Normal} : ℝ) *
        completeQuotientWeight (R := R) J := by
  have h := fusionCompleteSourceSum_le_axisEnvelopeTotal U P
    (fun _ => (1 : ℝ))
    (fun K => completeQuotientWeight (R := R) K)
    (fun (N : {N : Subgroup U // N.Normal})
        (K : Subgroup (Equiv.Perm (Fin b))) => by
      simpa only [one_mul] using
      fusionSurvivingEpiCount_le_completeQuotientWeight_of_comparator
        U P N (C N) K) J
  simpa only [fusionAxisEnvelopeTotal, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, Fintype.card_eq_nat_card, Nat.cast_ofNat, one_mul,
    mul_one] using h

end SymmetricSubgroupAsymptotics

end
