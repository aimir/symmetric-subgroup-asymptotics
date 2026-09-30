import SymmetricSubgroupAsymptotics.BinaryCarrierSourceExtraction

/-!
# Closure of the complete finite carrier source alphabet

A source occurrence is either an original action already in the completed
mixture alphabet or one of the four exceptional actions admitting a checked
reversible carrier.  Original occurrences retain their own literal normal
axes.  Exceptional occurrences retain the exact checked quotient map.  The
single theorem below handles arbitrary multiplicities and arbitrary mixtures
of these occurrences simultaneously.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.BinaryCarrierAlphabetWordClosure

open SymmetricSubgroupAsymptotics
open BinaryCarrierProfileTransport
open BinaryCarrierWordClosure
open BinaryCarrierMenuSlots

/-- The complete source alphabet for the carrier branch. -/
inductive SourceKind
  | original (g : MixtureKind)
  | exceptional (e : Exceptional)
  deriving DecidableEq, Fintype

variable (m : SourceKind → ℕ)

abbrev Occurrence := Σ s, Fin (m s)

variable
  (N : ∀ g, Fin (m (.original g)) → Subgroup (mixtureAction g))
  [∀ g j, (N g j).Normal]

/-- The local slot attached to each occurrence of the complete source
alphabet. -/
def wordSlot : Occurrence m → Slot
  | ⟨.original g,j⟩ => quotientIdentitySlot g (N g j)
  | ⟨.exceptional e,_⟩ => exceptionalSlot e

/-- On an unchanged occurrence, the slot's quotient kernel is the supplied
literal original normal axis. -/
theorem wordSlot_alpha_ker_original (g : MixtureKind)
    (j : Fin (m (.original g))) :
    (wordSlot m N ⟨.original g,j⟩).alpha.ker = N g j :=
  quotientIdentitySlot_alpha_ker g (N g j)

/-- The exact simultaneous source family for the whole source-alphabet
word.  It consists only of full original subgroups satisfying the displayed
axis equations. -/
abbrev SourceFamily :=
  CarrierTransportSource (alphas (wordSlot m N))

/-- The reversible source record exposes the prescribed literal normal axis
on every unchanged original-action occurrence. -/
theorem source_original_axis (H : SourceFamily m N)
    (g : MixtureKind) (j : Fin (m (.original g))) :
    carrierAxis H.1 ⟨.original g,j⟩ = N g j :=
  (H.2.2 ⟨.original g,j⟩).trans (wordSlot_alpha_ker_original m N g j)

/-- Arbitrary mixed words in the complete finite source alphabet enter the
completed mixture as soon as their source profile contains either an
unchanged noncritical colour or any exceptional occurrence. -/
theorem source_alphabet_word_card_le_mixture
    (hsupport :
      (∃ g, 0 < m (.original (.inr g))) ∨
        (∃ e, 0 < m (.exceptional e))) :
    Nat.card (SourceFamily m N) ≤
      Nat.card (BinaryCarrierMixtureCompletion.Family
        (parameter (cells (wordSlot m N)) (colors (wordSlot m N)))) := by
  apply slot_source_card_le_mixture
  rcases hsupport with ⟨g,hg⟩ | ⟨e,he⟩
  · let j : Fin (m (.original (.inr g))) := ⟨0,hg⟩
    let c : (wordSlot m N ⟨.original (.inr g),j⟩).Cells := by
      change Fin 1
      exact 0
    exact ⟨⟨⟨.original (.inr g),j⟩,c⟩,g,rfl⟩
  · let j : Fin (m (.exceptional e)) := ⟨0,he⟩
    obtain ⟨c,t,hc⟩ := exceptional_has_noncritical e
    exact ⟨⟨⟨.exceptional e,j⟩,c⟩,t,hc⟩

end SymmetricSubgroupAsymptotics.BinaryCarrierAlphabetWordClosure
