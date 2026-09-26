import SymmetricSubgroupAsymptotics.FaithfulFiniteActionImage
import SymmetricSubgroupAsymptotics.OriginalNormalChiefHead

/-! Explicit recognition of an original faithful action whose labelled
image contains the natural alternating group. Index two gives exactly
the alternating or symmetric image, and their existing symbolic chief
series transport back to the original ambient group. The inclusion is
an explicit hypothesis, not a primitive classification theorem. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics

variable {A Ω : Type} [Group A] [MulAction A Ω] {n : ℕ} (e : Ω ≃ Fin n)

theorem labelledActionImage_eq_alternating_or_top (hn : 5 ≤ n)
    (hAlt : alternatingGroup (Fin n) ≤ labelledActionImage (A := A) e) :
    labelledActionImage (A := A) e = alternatingGroup (Fin n) ∨
      labelledActionImage (A := A) e = ⊤ := by
  letI : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr (by omega)
  letI := alternatingGroup.isSimpleGroup (α := Fin n) (by simpa using hn)
  exact indexTwo_maximal (alternatingGroup (Fin n)) alternatingGroup.index_eq_two
    (labelledActionImage (A := A) e) hAlt

/-- An actual zero-weight chief series of the original ambient group,
under an explicit inclusion of the natural alternating group in its
faithful labelled image. The actual image may be alternating or symmetric. -/
theorem faithfulActionChiefSeries_zero_of_alternating_le [FaithfulSMul A Ω]
    (hn : 5 ≤ n)
    (hAlt : alternatingGroup (Fin n) ≤ labelledActionImage (A := A) e) :
    ∃ c : ActualChiefSeries A, actualChiefSeriesTernaryWeight c = 0 := by
  rcases labelledActionImage_eq_alternating_or_top e hn hAlt with hA | hS
  · exact alternatingChiefSeries_zero_of_equiv n hn
      ((faithfulLabelledActionEquiv e).trans (MulEquiv.subgroupCongr hA))
  · exact symmetricChiefSeries_zero_of_equiv n hn
      (((faithfulLabelledActionEquiv e).trans (MulEquiv.subgroupCongr hS)).trans
        Subgroup.topEquiv)

/-- Every original normal subgroup has zero relative ternary head in
the original ambient. No normal-subgroup catalogue or primitivity input
is needed once the actual image inclusion has been proved. -/
theorem faithfulActionRelativeHead_eq_zero_of_alternating_le [FaithfulSMul A Ω]
    (hn : 5 ≤ n)
    (hAlt : alternatingGroup (Fin n) ≤ labelledActionImage (A := A) e)
    (N : Subgroup A) [N.Normal] :
    Module.finrank (ZMod 3) (primeRelativeCharacters 3 N) = 0 := by
  letI : Finite A := faithfulLabelledAction_finite e
  obtain ⟨c, hc⟩ := faithfulActionChiefSeries_zero_of_alternating_le e hn hAlt
  exact primeRelativeHead_eq_zero_of_actualChiefWeight_zero N c hc

end SymmetricSubgroupAsymptotics
