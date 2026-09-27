import SymmetricSubgroupAsymptotics.BinaryPairLargeSectionCharacter
import SymmetricSubgroupAsymptotics.BinaryPairEightSmallSectionCuts

/-!
# Eight-pair sections: cut, original character, or dimension four

The actual fixed-section bound at pair exponent three is three. A section
of dimension greater than four has a faithful actual top action by the
checked large-section argument. Its original quotient therefore has the
same central-involution rank and satisfies the exact seven-power character
test at the original sixteen-point width.

Together with the checked small-section cut, this leaves precisely the
four-dimensional original section as a structural residue. No claim is
made that all axes in that residue pass either test.
-/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics.BinaryPairFrame

variable {X I : Type} {U : Subgroup (Equiv.Perm X)}
    (F : BinaryPairFrame U I) (N : Subgroup U) [N.Normal]

/-- The bound is on the full invariant space of the actual original
section, supplied by its original eight-point permutation realization. -/
theorem section_invariants_finrank_le_three_of_eight [Finite X] [Finite I]
    [MulAction.IsPretransitive F.top.range I] (hU : IsPGroup 2 U)
    (hI : Nat.card I=8) :
    Module.finrank (ZMod 2) (F.sectionRepresentation N).invariants≤3 := by
  have h := F.section_invariants_finrank_le_of_top N hU 3 (by simpa using hI)
  norm_num at h
  exact h

/-- Large sections on eight pair labels give a character criterion for
the unchanged original quotient U/N and its original physical width. -/
def largeSectionSevenCriterion_of_eight [Finite X] [Finite I]
    [MulAction.IsPretransitive F.top.range I] (hU : IsPGroup 2 U)
    (hI : Nat.card I=8)
    (hlarge : 4<Module.finrank (ZMod 2) (F.kernelSpace ⧸ F.normalSpace N)) :
    BinarySevenCharacterCriterion (U ⧸ N) (Nat.card X) := by
  have hnonempty : Nonempty I := (Nat.card_pos_iff.mp (by rw [hI]; decide)).1
  let i : I := Classical.choice hnonempty
  refine {
    dimension := Module.finrank (ZMod 2) (F.sectionRepresentation N).invariants
    cardinal := F.binaryCentralOmega_card_of_large N hU i (by rw [hI]; omega)
    gap := ?_ }
  rw [F.card_points,hI]
  apply binarySeven_character_gap_of_sixteen_mul_le _ _ (by decide)
  have hz := F.section_invariants_finrank_le_three_of_eight N hU hI
  omega

/-- Every actual original normal axis has either a strict actual cut,
an original-quotient character criterion, or an exactly four-dimensional
section. The final alternative is retained, not assumed accepted. -/
theorem eight_section_cut_or_character_or_dimension_four [Finite X] [Finite I]
    [MulAction.IsPretransitive F.top.range I] (hU : IsPGroup 2 U)
    (hI : Nat.card I=8) :
    (∃ (C : Submodule (ZMod 2) (F.kernelSpace ⧸ F.normalSpace N))
      (hC : C≤(F.sectionRepresentation N).invariants),
      (2:ℝ)*Module.finrank (ZMod 2) C+
        4*representationSchurCapacity (F.cutRepresentation N C hC)+2≤(Nat.card I:ℝ)) ∨
      Nonempty (BinarySevenCharacterCriterion (U ⧸ N) (Nat.card X)) ∨
      Module.finrank (ZMod 2) (F.kernelSpace ⧸ F.normalSpace N)=4 := by
  by_cases hsmall : Module.finrank (ZMod 2) (F.kernelSpace ⧸ F.normalSpace N)≤3
  · exact Or.inl (F.exists_eight_small_section_cut N hU hI hsmall)
  by_cases hlarge : 4<Module.finrank (ZMod 2) (F.kernelSpace ⧸ F.normalSpace N)
  · exact Or.inr (Or.inl ⟨F.largeSectionSevenCriterion_of_eight N hU hI hlarge⟩)
  · exact Or.inr (Or.inr (by omega))

/-- Away from the explicit dimension-four residue, acceptance is proved
on the literal original section and quotient, with no supplied certificate. -/
theorem eight_section_cut_or_character_of_dimension_ne_four [Finite X] [Finite I]
    [MulAction.IsPretransitive F.top.range I] (hU : IsPGroup 2 U)
    (hI : Nat.card I=8)
    (hfour : Module.finrank (ZMod 2) (F.kernelSpace ⧸ F.normalSpace N)≠4) :
    (∃ (C : Submodule (ZMod 2) (F.kernelSpace ⧸ F.normalSpace N))
      (hC : C≤(F.sectionRepresentation N).invariants),
      (2:ℝ)*Module.finrank (ZMod 2) C+
        4*representationSchurCapacity (F.cutRepresentation N C hC)+2≤(Nat.card I:ℝ)) ∨
      Nonempty (BinarySevenCharacterCriterion (U ⧸ N) (Nat.card X)) := by
  rcases F.eight_section_cut_or_character_or_dimension_four N hU hI with h | h | h
  · exact Or.inl h
  · exact Or.inr h
  · exact (hfour h).elim

end SymmetricSubgroupAsymptotics.BinaryPairFrame
