import SymmetricSubgroupAsymptotics.BinaryDegreeEightPhysicalAnalyticClosure
import SymmetricSubgroupAsymptotics.FusionQuotientComparator

/-!
# Quotient comparators retained by an exact carrier axis slot

An `AxisSlot A N` already says that, after the stored source equivalence,
the literal normal axis `N` is exactly the kernel of the carrier source map.
The carrier map has the same quotient.  Consequently `A/N` is a literal
normal quotient of the proper carrier itself.

This is the local incidence statement needed by the affine four-block cell.
It keeps the selected carrier and the selected normal axis correlated; no
maximum over carrier routes is taken.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace BinaryCarrierAxisSlotComparator

open BinaryDegreeEightPhysicalAnalyticClosure

variable {A : Type} [Group A] {N : Subgroup A}

/-- The source quotient map of an exact axis slot, pulled back to the
literal source group. -/
def sourceAlpha (S : AxisSlot A N) : A →* S.slot.Quotient :=
  S.slot.alpha.comp S.sourceEquiv.toMonoidHom

theorem sourceAlpha_surjective (S : AxisSlot A N) :
    Function.Surjective (sourceAlpha S) :=
  S.slot.alphaSurjective.comp S.sourceEquiv.surjective

/-- The retained axis equation is exactly the kernel equation on the
literal source. -/
theorem sourceAlpha_ker (S : AxisSlot A N) :
    (sourceAlpha S).ker = N := by
  ext a
  constructor
  · intro ha
    have hea : S.sourceEquiv a ∈ S.slot.alpha.ker := ha
    rw [← S.kernel] at hea
    obtain ⟨n, hn, hna⟩ := hea
    have : n = a := S.sourceEquiv.injective hna
    exact this ▸ hn
  · intro ha
    have hea : S.sourceEquiv a ∈ N.map S.sourceEquiv.toMonoidHom :=
      ⟨a, ha, rfl⟩
    rw [S.kernel] at hea
    exact hea

/-- The literal source quotient is the common quotient stored by the slot. -/
def sourceQuotientEquiv [N.Normal] (S : AxisSlot A N) :
    A ⧸ N ≃* S.slot.Quotient :=
  (QuotientGroup.quotientMulEquivOfEq (sourceAlpha_ker S).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective
      (sourceAlpha S) (sourceAlpha_surjective S))

/-- The displayed proper carrier has the same common quotient. -/
def carrierQuotientEquiv (S : AxisSlot A N) :
    S.slot.carrier ⧸ S.slot.beta.ker ≃* S.slot.Quotient :=
  QuotientGroup.quotientKerEquivOfSurjective
    S.slot.beta S.slot.betaSurjective

/-- Counting form: epimorphisms to the selected source quotient are one
literal normal-axis summand of the selected carrier's complete quotient
weight. -/
theorem epi_card_le_completeQuotientWeight
    [N.Normal]
    (S : AxisSlot A N) {b : ℕ}
    (J : Subgroup (Equiv.Perm (Fin b))) :
    (Nat.card (GroupEpimorphism J (A ⧸ N)) : ℝ) ≤
      completeQuotientWeight (R := S.slot.carrier) J := by
  let M : {M : Subgroup S.slot.carrier // M.Normal} :=
    ⟨S.slot.beta.ker, inferInstance⟩
  have htransport : Nat.card (GroupEpimorphism J (A ⧸ N)) =
      Nat.card (GroupEpimorphism J (S.slot.carrier ⧸ M.1)) :=
    fusionGroupEpimorphism_card_congr (MulEquiv.refl J)
      ((sourceQuotientEquiv S).trans (carrierQuotientEquiv S).symm)
  have haxis : Nat.card (GroupEpimorphism J
      (S.slot.carrier ⧸ M.1)) ≤
      completeQuotientCount (R := S.slot.carrier) J := by
    unfold completeQuotientCount
    exact Finset.single_le_sum
      (fun K _ ↦ Nat.zero_le
        (Nat.card (GroupEpimorphism J (S.slot.carrier ⧸ K.1))))
      (Finset.mem_univ M)
  unfold completeQuotientWeight
  exact_mod_cast htransport.le.trans haxis

end BinaryCarrierAxisSlotComparator
end SymmetricSubgroupAsymptotics

end
