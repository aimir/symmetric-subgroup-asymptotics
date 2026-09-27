import SymmetricSubgroupAsymptotics.BinaryPairRankTwoTwistCharacter
import SymmetricSubgroupAsymptotics.BinaryPairRankTwoZeroParity

/-!
# The complete eight-pair reduction with actual parity resolved

The remaining rank-two action either has a small original target, satisfies
the exact character criterion on U/N, or is physically conjugate to its
split action. In the last branch the entire original residual, including
the normal-image guard, is retained. Matching these split actions to the
existing carrier owners remains a separate obligation.
-/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics.BinaryPairFrame

variable {X I : Type} {U : Subgroup (Equiv.Perm X)}
    (F : BinaryPairFrame U I) (N : Subgroup U) [N.Normal]
    [Finite X] [Finite I] [MulAction.IsPretransitive F.top.range I]
    (hU : IsPGroup 2 U) (hI : Nat.card I = 8)

include hU hI in
theorem eight_rank_two_order_character_or_split
    (hres : F.EightPairRankTwoResidual N) :
    (Nat.card U ≤ 2048 ∧ Nat.card (U ⧸ N) ≤ 128) ∨
    Nonempty (BinarySevenCharacterCriterion (U ⧸ N) (Nat.card X)) ∨
    (∃ a : I → ZMod 2,
      U.map (MulAut.conj (F.physicalFlip a)).toMonoidHom = F.splitAffineAction) := by
  obtain ⟨htop,hsource,htarget,_,_⟩ := F.eight_rank_two_original_orders N hU hI hres
  by_cases hsmall : Nat.card F.top.range = 8
  · exact Or.inl ⟨by rcases hsource with h | h | h <;> omega, htarget hsmall⟩
  have hlarge : 8 < Nat.card F.top.range := by
    rcases htop with h | h | h <;> omega
  by_cases hp : ∃ h, F.rankTwoTranslationParity N hU hI hres hlarge h ≠ 0
  · exact Or.inr (Or.inl ⟨F.rankTwoNonzeroParitySevenCriterion N hU hI hres hlarge hp⟩)
  · exact Or.inr (Or.inr (F.rankTwo_zero_first_parity_physical_conjugate N
      hU hI hres hlarge (fun h => not_ne_iff.mp (fun hh => hp ⟨h,hh⟩))))

/-- The last alternative retains the original normal and all its guards;
physical source conjugacy alone is not a carrier-acceptance certificate. -/
def EightPairPhysicalReduction : Prop :=
  (∃ (C : Submodule (ZMod 2) (F.kernelSpace ⧸ F.normalSpace N))
    (hC : C ≤ (F.sectionRepresentation N).invariants),
    (2 : ℝ) * Module.finrank (ZMod 2) C +
      4 * representationSchurCapacity (F.cutRepresentation N C hC) ≤ 6) ∨
  (Nat.card U ≤ 2048 ∧ Nat.card (U ⧸ N) ≤ 128) ∨
  Nonempty (BinarySevenCharacterCriterion (U ⧸ N) (Nat.card X)) ∨
  (F.EightPairRankTwoResidual N ∧ ∃ a : I → ZMod 2,
    U.map (MulAut.conj (F.physicalFlip a)).toMonoidHom = F.splitAffineAction)

include hU hI in
/-- Every original eight-pair axis enters one of these alternatives.
There is no parity, section-dimension, chart, or carrier-completeness premise. -/
theorem eight_section_physical_reduction : F.EightPairPhysicalReduction N := by
  rcases F.eight_section_residual_reduction N hU hI with hcut | horder | hchar | hres
  · exact Or.inl hcut
  · exact Or.inr (Or.inl ⟨horder.1.trans (by decide), horder.2⟩)
  · exact Or.inr (Or.inr (Or.inl hchar))
  · rcases F.eight_rank_two_order_character_or_split N hU hI hres with horder | hchar | hsplit
    · exact Or.inr (Or.inl horder)
    · exact Or.inr (Or.inr (Or.inl hchar))
    · exact Or.inr (Or.inr (Or.inr ⟨hres,hsplit⟩))

end SymmetricSubgroupAsymptotics.BinaryPairFrame
