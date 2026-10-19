import SymmetricSubgroupAsymptotics.MarkedC4ActualNormalizedWordPeel

/-! Actual one-step fibre decoder when the original normal menu is FIXED
by the global history. No normal-menu factor is charged at this step. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.MarkedC4.ActualFixedNormalWordPeel
open ActualFullPhysicalWordPeel ActualWholeWordPackets

variable {t : ℕ} (F : Fin (t+1) → Type) [∀ i,Group (F i)] [∀ i,Finite (F i)]
  (M : Type) [Group M] (N : Menu F)
local instance normalAt (i : Fin (t+1)) : (N i).val.Normal := (N i).property

abbrev Family := {J : ActualFullPhysicalWordPeel.Family F M // actualMenu F M J=N}

def normalize (J : Family F M N) : NormalizedFamily F M N := by
  rcases J with ⟨J,hJ⟩
  exact hJ ▸ (ActualWholeWordPackets.code F M J).2

def decodeNormalized (A : NormalizedFamily F M N) : Subgroup ((∀ i,F i) × M) :=
  A.val.val.comap (ActualWholeWordPackets.quotientMap F M N)

theorem normalize_recover (J : Family F M N) :
    decodeNormalized F M N (normalize F M N J)=J.val.val := by
  rcases J with ⟨J,hJ⟩
  cases hJ
  exact ActualWholeWordPackets.recover F M J

theorem normalize_injective : Function.Injective (normalize F M N) := by
  intro J K he
  apply Subtype.ext
  apply Subtype.ext
  exact (normalize_recover F M N J).symm.trans
    ((congrArg (decodeNormalized F M N) he).trans (normalize_recover F M N K))

def code (J : Family F M N) : ActualNormalizedWordPeel.Packet (Factors F N) M :=
  ActualNormalizedWordPeel.code (Factors F N) M (normalize F M N J)

theorem code_injective : Function.Injective (code F M N) := by
  intro J K he
  apply normalize_injective F M N
  exact ActualNormalizedWordPeel.code_injective (Factors F N) M he

/-- The current original normal menu has already been selected globally.
The only remaining alternatives are actual smaller marked sources and
actual epi fibres of the removed quotient target. -/
theorem card_le_packets [Finite M] :
    Nat.card (Family F M N)≤Nat.card (ActualNormalizedWordPeel.Packet (Factors F N) M) :=
  Nat.card_le_card_of_injective (code F M N) (code_injective F M N)

end SymmetricSubgroupAsymptotics.MarkedC4.ActualFixedNormalWordPeel
