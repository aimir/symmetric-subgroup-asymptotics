import SymmetricSubgroupAsymptotics.BinaryCarrierCrossing16
import SymmetricSubgroupAsymptotics.NormalSubgroupSaturationHeadBounds
import SymmetricSubgroupAsymptotics.BinaryCarrierRadicalHead16T1547
import Mathlib.Data.Nat.Log
import Lean.Elab.Tactic.Omega

/-! Exact capacities of the original derived intersection in every crossing
normal of the four pair-family masters. The maximum includes every original
ambient-normal subgroup of the intersection. It is not a maximum over a
stored profile list. The second radical belongs to the same original N. -/
set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics

private theorem relativeHead_eq_of_subgroup_eq
    (p : ℕ) [Fact p.Prime] {G : Type*} [Group G]
    (M P : Subgroup G) [M.Normal] [P.Normal] (h : M = P) :
    Module.finrank (ZMod p) (primeRelativeCharacters p M) =
      Module.finrank (ZMod p) (primeRelativeCharacters p P) := by
  subst P
  rfl

namespace BinaryCarrierCrossingCapacity16T1082

abbrev Original := BinaryCarrierCrossing16T1082.Original

private theorem intersection_not_le_radical (N : Subgroup Original) [N.Normal]
    (hnotND : ¬N ≤ commutator Original) :
    ¬N ⊓ commutator Original ≤ primeRelativeRadical 2 (commutator Original) :=
  fun h => hnotND
    (BinaryCarrierProperIntersection16T1082.normal_le_derived_of_intersection_le_radical N h)

theorem intersection_relative_radical_eq (N : Subgroup Original) [N.Normal]
    (hnotND : ¬N ≤ commutator Original) :
    primeRelativeRadical 2 (N ⊓ commutator Original) =
      primeRelativeRadical 2 (commutator Original) :=
  BinaryCarrierRadicalSaturation16T1082.certificate.relativeRadical_eq 2
    BinaryCarrierRadicalSaturation16T1082.nonempty_words
    (N ⊓ commutator Original) inf_le_right (intersection_not_le_radical N hnotND)

theorem intersection_head_eq_two (N : Subgroup Original) [N.Normal]
    (hnotND : ¬N ≤ commutator Original) (hnotDN : ¬commutator Original ≤ N) :
    Module.finrank (ZMod 2) (primeRelativeCharacters 2 (N ⊓ commutator Original)) = 2 := by
  have h := primeRelativeHead_add_one_eq_of_relativeRadical_eq_and_card 2
    (N ⊓ commutator Original) (commutator Original)
    (intersection_relative_radical_eq N hnotND)
    (BinaryCarrierCrossing16T1082.exact_quotient_invariants N hnotND hnotDN).2.2.1
  rw [BinaryCarrierDerivedRadical16T1082.relative_character_rank] at h
  omega

theorem radical_normalHeadMax_le_two :
    primeNormalHeadMax 2 (primeRelativeRadical 2 (commutator Original)) ≤ 2 := by
  have h := primeNormalHeadMax_le_log_card 2
    (primeRelativeRadical 2 (commutator Original))
  rw [BinaryCarrierDerivedRadical16T1082.card_relative_radical] at h
  have hlog : Nat.log 2 2 = 1 := by decide
  rw [hlog] at h
  exact h.trans (by decide)

theorem intersection_normalHeadMax_eq_two (N : Subgroup Original) [N.Normal]
    (hnotND : ¬N ≤ commutator Original) (hnotDN : ¬commutator Original ≤ N) :
    primeNormalHeadMax 2 (N ⊓ commutator Original) = 2 := by
  rw [BinaryCarrierRadicalSaturation16T1082.certificate.normalHeadMax_eq_max 2
    BinaryCarrierRadicalSaturation16T1082.nonempty_words
    (N ⊓ commutator Original) inf_le_right (intersection_not_le_radical N hnotND),
    intersection_head_eq_two N hnotND hnotDN]
  exact max_eq_right radical_normalHeadMax_le_two

theorem second_radical_head_eq_two (N : Subgroup Original) [N.Normal]
    (hnotND : ¬N ≤ commutator Original) (hnotDN : ¬commutator Original ≤ N) :
    Module.finrank (ZMod 2) (primeRelativeCharacters 2 (primeRelativeRadical 2 N)) = 2 := by
  exact (relativeHead_eq_of_subgroup_eq 2 _ _
    (BinaryCarrierCrossing16T1082.relative_radical_eq_intersection N hnotND hnotDN)).trans
      (intersection_head_eq_two N hnotND hnotDN)

end BinaryCarrierCrossingCapacity16T1082

namespace BinaryCarrierCrossingCapacity16T1083

abbrev Original := BinaryCarrierCrossing16T1083.Original

private theorem intersection_not_le_radical (N : Subgroup Original) [N.Normal]
    (hnotND : ¬N ≤ commutator Original) :
    ¬N ⊓ commutator Original ≤ primeRelativeRadical 2 (commutator Original) :=
  fun h => hnotND
    (BinaryCarrierProperIntersection16T1083.normal_le_derived_of_intersection_le_radical N h)

theorem intersection_relative_radical_eq (N : Subgroup Original) [N.Normal]
    (hnotND : ¬N ≤ commutator Original) :
    primeRelativeRadical 2 (N ⊓ commutator Original) =
      primeRelativeRadical 2 (commutator Original) :=
  BinaryCarrierRadicalSaturation16T1083.certificate.relativeRadical_eq 2
    BinaryCarrierRadicalSaturation16T1083.nonempty_words
    (N ⊓ commutator Original) inf_le_right (intersection_not_le_radical N hnotND)

theorem intersection_head_eq_two (N : Subgroup Original) [N.Normal]
    (hnotND : ¬N ≤ commutator Original) (hnotDN : ¬commutator Original ≤ N) :
    Module.finrank (ZMod 2) (primeRelativeCharacters 2 (N ⊓ commutator Original)) = 2 := by
  have h := primeRelativeHead_add_one_eq_of_relativeRadical_eq_and_card 2
    (N ⊓ commutator Original) (commutator Original)
    (intersection_relative_radical_eq N hnotND)
    (BinaryCarrierCrossing16T1083.exact_quotient_invariants N hnotND hnotDN).2.2.1
  rw [BinaryCarrierDerivedRadical16T1083.relative_character_rank] at h
  omega

theorem radical_normalHeadMax_le_two :
    primeNormalHeadMax 2 (primeRelativeRadical 2 (commutator Original)) ≤ 2 := by
  have h := primeNormalHeadMax_le_log_card 2
    (primeRelativeRadical 2 (commutator Original))
  rw [BinaryCarrierDerivedRadical16T1083.card_relative_radical] at h
  have hlog : Nat.log 2 2 = 1 := by decide
  rw [hlog] at h
  exact h.trans (by decide)

theorem intersection_normalHeadMax_eq_two (N : Subgroup Original) [N.Normal]
    (hnotND : ¬N ≤ commutator Original) (hnotDN : ¬commutator Original ≤ N) :
    primeNormalHeadMax 2 (N ⊓ commutator Original) = 2 := by
  rw [BinaryCarrierRadicalSaturation16T1083.certificate.normalHeadMax_eq_max 2
    BinaryCarrierRadicalSaturation16T1083.nonempty_words
    (N ⊓ commutator Original) inf_le_right (intersection_not_le_radical N hnotND),
    intersection_head_eq_two N hnotND hnotDN]
  exact max_eq_right radical_normalHeadMax_le_two

theorem second_radical_head_eq_two (N : Subgroup Original) [N.Normal]
    (hnotND : ¬N ≤ commutator Original) (hnotDN : ¬commutator Original ≤ N) :
    Module.finrank (ZMod 2) (primeRelativeCharacters 2 (primeRelativeRadical 2 N)) = 2 := by
  exact (relativeHead_eq_of_subgroup_eq 2 _ _
    (BinaryCarrierCrossing16T1083.relative_radical_eq_intersection N hnotND hnotDN)).trans
      (intersection_head_eq_two N hnotND hnotDN)

end BinaryCarrierCrossingCapacity16T1083

namespace BinaryCarrierCrossingCapacity16T1084

abbrev Original := BinaryCarrierCrossing16T1084.Original

private theorem intersection_not_le_radical (N : Subgroup Original) [N.Normal]
    (hnotND : ¬N ≤ commutator Original) :
    ¬N ⊓ commutator Original ≤ primeRelativeRadical 2 (commutator Original) :=
  fun h => hnotND
    (BinaryCarrierProperIntersection16T1084.normal_le_derived_of_intersection_le_radical N h)

theorem intersection_relative_radical_eq (N : Subgroup Original) [N.Normal]
    (hnotND : ¬N ≤ commutator Original) :
    primeRelativeRadical 2 (N ⊓ commutator Original) =
      primeRelativeRadical 2 (commutator Original) :=
  BinaryCarrierRadicalSaturation16T1084.certificate.relativeRadical_eq 2
    BinaryCarrierRadicalSaturation16T1084.nonempty_words
    (N ⊓ commutator Original) inf_le_right (intersection_not_le_radical N hnotND)

theorem intersection_head_eq_two (N : Subgroup Original) [N.Normal]
    (hnotND : ¬N ≤ commutator Original) (hnotDN : ¬commutator Original ≤ N) :
    Module.finrank (ZMod 2) (primeRelativeCharacters 2 (N ⊓ commutator Original)) = 2 := by
  have h := primeRelativeHead_add_one_eq_of_relativeRadical_eq_and_card 2
    (N ⊓ commutator Original) (commutator Original)
    (intersection_relative_radical_eq N hnotND)
    (BinaryCarrierCrossing16T1084.exact_quotient_invariants N hnotND hnotDN).2.2.1
  rw [BinaryCarrierDerivedRadical16T1084.relative_character_rank] at h
  omega

theorem radical_normalHeadMax_le_two :
    primeNormalHeadMax 2 (primeRelativeRadical 2 (commutator Original)) ≤ 2 := by
  have h := primeNormalHeadMax_le_log_card 2
    (primeRelativeRadical 2 (commutator Original))
  rw [BinaryCarrierDerivedRadical16T1084.card_relative_radical] at h
  have hlog : Nat.log 2 2 = 1 := by decide
  rw [hlog] at h
  exact h.trans (by decide)

theorem intersection_normalHeadMax_eq_two (N : Subgroup Original) [N.Normal]
    (hnotND : ¬N ≤ commutator Original) (hnotDN : ¬commutator Original ≤ N) :
    primeNormalHeadMax 2 (N ⊓ commutator Original) = 2 := by
  rw [BinaryCarrierRadicalSaturation16T1084.certificate.normalHeadMax_eq_max 2
    BinaryCarrierRadicalSaturation16T1084.nonempty_words
    (N ⊓ commutator Original) inf_le_right (intersection_not_le_radical N hnotND),
    intersection_head_eq_two N hnotND hnotDN]
  exact max_eq_right radical_normalHeadMax_le_two

theorem second_radical_head_eq_two (N : Subgroup Original) [N.Normal]
    (hnotND : ¬N ≤ commutator Original) (hnotDN : ¬commutator Original ≤ N) :
    Module.finrank (ZMod 2) (primeRelativeCharacters 2 (primeRelativeRadical 2 N)) = 2 := by
  exact (relativeHead_eq_of_subgroup_eq 2 _ _
    (BinaryCarrierCrossing16T1084.relative_radical_eq_intersection N hnotND hnotDN)).trans
      (intersection_head_eq_two N hnotND hnotDN)

end BinaryCarrierCrossingCapacity16T1084

namespace BinaryCarrierCrossingCapacity16T1547

abbrev Original := BinaryCarrierCrossing16T1547.Original

private theorem intersection_not_le_radical (N : Subgroup Original) [N.Normal]
    (hnotND : ¬N ≤ commutator Original) :
    ¬N ⊓ commutator Original ≤ primeRelativeRadical 2 (commutator Original) :=
  fun h => hnotND
    (BinaryCarrierProperIntersection16T1547.normal_le_derived_of_intersection_le_radical N h)

theorem intersection_relative_radical_eq (N : Subgroup Original) [N.Normal]
    (hnotND : ¬N ≤ commutator Original) :
    primeRelativeRadical 2 (N ⊓ commutator Original) =
      primeRelativeRadical 2 (commutator Original) :=
  BinaryCarrierRadicalSaturation16T1547.certificate.relativeRadical_eq 2
    BinaryCarrierRadicalSaturation16T1547.nonempty_words
    (N ⊓ commutator Original) inf_le_right (intersection_not_le_radical N hnotND)

theorem intersection_head_eq_two (N : Subgroup Original) [N.Normal]
    (hnotND : ¬N ≤ commutator Original) (hnotDN : ¬commutator Original ≤ N) :
    Module.finrank (ZMod 2) (primeRelativeCharacters 2 (N ⊓ commutator Original)) = 2 := by
  have h := primeRelativeHead_add_one_eq_of_relativeRadical_eq_and_card 2
    (N ⊓ commutator Original) (commutator Original)
    (intersection_relative_radical_eq N hnotND)
    (BinaryCarrierCrossing16T1547.exact_quotient_invariants N hnotND hnotDN).2.2.1
  rw [BinaryCarrierDerivedRadical16T1547.relative_character_rank] at h
  omega

theorem radical_normalHeadMax_le_two :
    primeNormalHeadMax 2 (primeRelativeRadical 2 (commutator Original)) ≤ 2 := by
  exact BinaryCarrierRadicalHead16T1547.normalHeadMax_le_two

theorem intersection_normalHeadMax_eq_two (N : Subgroup Original) [N.Normal]
    (hnotND : ¬N ≤ commutator Original) (hnotDN : ¬commutator Original ≤ N) :
    primeNormalHeadMax 2 (N ⊓ commutator Original) = 2 := by
  rw [BinaryCarrierRadicalSaturation16T1547.certificate.normalHeadMax_eq_max 2
    BinaryCarrierRadicalSaturation16T1547.nonempty_words
    (N ⊓ commutator Original) inf_le_right (intersection_not_le_radical N hnotND),
    intersection_head_eq_two N hnotND hnotDN]
  exact max_eq_right radical_normalHeadMax_le_two

theorem second_radical_head_eq_two (N : Subgroup Original) [N.Normal]
    (hnotND : ¬N ≤ commutator Original) (hnotDN : ¬commutator Original ≤ N) :
    Module.finrank (ZMod 2) (primeRelativeCharacters 2 (primeRelativeRadical 2 N)) = 2 := by
  exact (relativeHead_eq_of_subgroup_eq 2 _ _
    (BinaryCarrierCrossing16T1547.relative_radical_eq_intersection N hnotND hnotDN)).trans
      (intersection_head_eq_two N hnotND hnotDN)

end BinaryCarrierCrossingCapacity16T1547

end SymmetricSubgroupAsymptotics
