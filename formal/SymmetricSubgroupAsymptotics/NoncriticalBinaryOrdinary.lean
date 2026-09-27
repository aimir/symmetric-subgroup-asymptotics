import SymmetricSubgroupAsymptotics.BinaryFamilies
import SymmetricSubgroupAsymptotics.EvenCriticalLiteral

/-!
# The even binary error inside the ordinary remainder

The intrinsic noncritical binary family is carried unchanged into the
literal complement of the complete parity-defined critical family.  This is
the even zero-defect ownership statement used by the ordinary recurrence.
-/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics.NoncriticalBinaryOrdinary

theorem not_isCritical (N : ℕ) (H : NoncriticalBinarySubgroups N) :
    ¬ IsCriticalSubgroup (2*N) H.val := by
  intro hcrit
  obtain ⟨J,hJ⟩ := (isCriticalSubgroup_even_iff N H.val).mp hcrit
  apply H.property.2
  obtain ⟨p,e,K,hK,hKJ⟩ := J.property
  exact ⟨p,e,K,hK,hKJ.trans hJ⟩

def embedding (N : ℕ) :
    NoncriticalBinarySubgroups N ↪ OrdinaryRemainderSubgroups (2*N) where
  toFun H := ⟨H.val,not_isCritical N H⟩
  inj' := by
    intro H K h
    apply Subtype.ext
    exact congrArg (fun L : OrdinaryRemainderSubgroups (2*N) => L.val) h

theorem card_le_ordinaryRemainder (N : ℕ) :
    Nat.card (NoncriticalBinarySubgroups N) ≤
      Nat.card (OrdinaryRemainderSubgroups (2*N)) :=
  Nat.card_le_card_of_injective (embedding N) (embedding N).injective

theorem binaryErrorRatio_le_ordinaryRemainderRatio (N : ℕ) :
    binaryErrorRatio N ≤ ordinaryRemainderRatio (2*N) := by
  unfold binaryErrorRatio ordinaryRemainderRatio
  exact div_le_div_of_nonneg_right
    (by exact_mod_cast card_le_ordinaryRemainder N)
    (exactBenchmark_pos _).le

end SymmetricSubgroupAsymptotics.NoncriticalBinaryOrdinary

end
