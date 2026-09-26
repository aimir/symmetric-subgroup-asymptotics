import SymmetricSubgroupAsymptotics.BinaryCarrierRadicalSaturation16T1332
import SymmetricSubgroupAsymptotics.BinaryCarrierExactOrders16
import SymmetricSubgroupAsymptotics.PrimeDerivedStarCrossing
import SymmetricSubgroupAsymptotics.NormalSubgroupSaturationHeadBounds
import SymmetricSubgroupAsymptotics.PrimeNormalHeadOrder

/-! Crossing normals of the literal 16T1332 action, using the complete
four-parameter star family and its actual nonempty saturation words.
The vanishing parameter dimension is retained throughout. The mixed
commutator need not equal the derived intersection; original powers can
only improve the head bound. No normal-menu or carrier-weight coverage
is asserted here. -/
set_option autoImplicit false
noncomputable section
open scoped commutatorElement

namespace SymmetricSubgroupAsymptotics.BinaryCarrierStarCrossing16T1332

abbrev Original := BinaryCarrierDerivedOrder16T1332.Original
private abbrev kernelIdentity := BinaryCarrierDerived16T1332.evaluationKernel_eq_commutator

private theorem horizontal_finrank :
    Module.finrank (ZMod 2) BinaryCarrierStarTransport16T1332.U = 4 := by simp

theorem radical_le_mixed (N : Subgroup Original) [N.Normal]
    (hnotND : ¬N ≤ commutator Original) (hnotDN : ¬commutator Original ≤ N) :
    primeRelativeRadical 2 (commutator Original) ≤ ⁅N, (⊤ : Subgroup Original)⁆ :=
  starDerived_radical_le_mixed_of_comparability 2 kernelIdentity
    BinaryCarrierExactOrder16T1332.original_isPGroup
    BinaryCarrierStarTransport16T1332.characterEquiv
    BinaryCarrierStarTransport16T1332.evaluationEquiv
    BinaryCarrierStarTransport16T1332.actual_form_eq_star
    BinaryCarrierRadicalSaturation16T1332.normal_comparable N hnotND hnotDN

theorem radical_le_intersection (N : Subgroup Original) [N.Normal]
    (hnotND : ¬N ≤ commutator Original) (hnotDN : ¬commutator Original ≤ N) :
    primeRelativeRadical 2 (commutator Original) ≤ N ⊓ commutator Original :=
  (radical_le_mixed N hnotND hnotDN).trans
    (le_inf (Subgroup.commutator_le_left N ⊤) (Subgroup.commutator_mono le_top le_rfl))

theorem intersection_not_le_radical (N : Subgroup Original) [N.Normal]
    (hnotND : ¬N ≤ commutator Original) (hnotDN : ¬commutator Original ≤ N) :
    ¬N ⊓ commutator Original ≤ primeRelativeRadical 2 (commutator Original) := by
  intro hB
  apply starDerived_mixedCommutator_not_le_radical 2 kernelIdentity
    BinaryCarrierExactOrder16T1332.original_isPGroup
    BinaryCarrierStarTransport16T1332.characterEquiv
    BinaryCarrierStarTransport16T1332.evaluationEquiv
    BinaryCarrierStarTransport16T1332.actual_form_eq_star N hnotND hnotDN
  exact (le_inf (Subgroup.commutator_le_left N ⊤)
    (Subgroup.commutator_mono le_top le_rfl)).trans hB

theorem image_one_le (N : Subgroup Original) (hnotND : ¬N ≤ commutator Original) :
    1 ≤ Module.finrank (ZMod 2) (primeDerivedImage 2 N) := by
  apply Submodule.one_le_finrank_iff.mpr
  intro hz
  exact hnotND ((primeDerivedImage_eq_bot_iff_le_commutator 2 kernelIdentity N).mp hz)

theorem vanishing_one_le (N : Subgroup Original) [N.Normal]
    (hnotDN : ¬commutator Original ≤ N) :
    1 ≤ Module.finrank (ZMod 2)
      (derivedCharactersVanishingOn 2 (N ⊓ commutator Original)) :=
  derivedCharactersVanishingOn_one_le_of_lt 2 BinaryCarrierExactOrder16T1332.original_isPGroup
    _ (derivedIntersection_lt_of_not_derived_le N hnotDN)

theorem image_add_vanishing_le_four (N : Subgroup Original) [N.Normal]
    (hnotDN : ¬commutator Original ≤ N) :
    Module.finrank (ZMod 2) (primeDerivedImage 2 N) +
      Module.finrank (ZMod 2) (derivedCharactersVanishingOn 2 (N ⊓ commutator Original)) ≤ 4 := by
  simpa only [horizontal_finrank] using
    primeDerivedImage_finrank_add_vanishing_le_of_star 2 kernelIdentity
      BinaryCarrierStarTransport16T1332.characterEquiv
      BinaryCarrierStarTransport16T1332.evaluationEquiv
      BinaryCarrierStarTransport16T1332.actual_form_eq_star
      (N ⊓ commutator Original) N le_rfl
      (Submodule.one_le_finrank_iff.mp (vanishing_one_le N hnotDN))

theorem head_add_vanishing_le_four (N : Subgroup Original) [N.Normal]
    (hnotND : ¬N ≤ commutator Original) (hnotDN : ¬commutator Original ≤ N) :
    Module.finrank (ZMod 2) (primeRelativeCharacters 2 N) +
      Module.finrank (ZMod 2) (derivedCharactersVanishingOn 2 (N ⊓ commutator Original)) ≤ 4 := by
  simpa only [horizontal_finrank] using
    primeRelativeHead_add_vanishing_le_of_star_crossing 2 kernelIdentity
      BinaryCarrierExactOrder16T1332.original_isPGroup
      BinaryCarrierStarTransport16T1332.characterEquiv
      BinaryCarrierStarTransport16T1332.evaluationEquiv
      BinaryCarrierStarTransport16T1332.actual_form_eq_star
      BinaryCarrierRadicalSaturation16T1332.normal_comparable N hnotND hnotDN

theorem intersection_radical_eq (N : Subgroup Original) [N.Normal]
    (hnotND : ¬N ≤ commutator Original) (hnotDN : ¬commutator Original ≤ N) :
    primeRelativeRadical 2 (N ⊓ commutator Original) =
      primeRelativeRadical 2 (commutator Original) :=
  BinaryCarrierRadicalSaturation16T1332.certificate.relativeRadical_eq 2
    BinaryCarrierRadicalSaturation16T1332.nonempty_words
    (N ⊓ commutator Original) inf_le_right (intersection_not_le_radical N hnotND hnotDN)

theorem intersection_head_add_vanishing_eq_four (N : Subgroup Original) [N.Normal]
    (hnotND : ¬N ≤ commutator Original) (hnotDN : ¬commutator Original ≤ N) :
    Module.finrank (ZMod 2) (derivedCharactersVanishingOn 2 (N ⊓ commutator Original)) +
      Module.finrank (ZMod 2) (primeRelativeCharacters 2 (N ⊓ commutator Original)) = 4 := by
  simpa only [BinaryCarrierDerivedRadical16T1332.relative_character_rank] using
    primeRelativeVanishing_finrank_add_head_of_radical_eq 2 (commutator Original)
      (N ⊓ commutator Original) inf_le_right (intersection_radical_eq N hnotND hnotDN)

theorem intersection_head_eq (N : Subgroup Original) [N.Normal]
    (hnotND : ¬N ≤ commutator Original) (hnotDN : ¬commutator Original ≤ N) :
    Module.finrank (ZMod 2) (primeRelativeCharacters 2 (N ⊓ commutator Original)) =
      4 - Module.finrank (ZMod 2) (derivedCharactersVanishingOn 2 (N ⊓ commutator Original)) := by
  have h := intersection_head_add_vanishing_eq_four N hnotND hnotDN
  omega

theorem normalHeadMax_radical_le_two :
    primeNormalHeadMax 2 (primeRelativeRadical 2 (commutator Original)) ≤ 2 := by
  have h := primeNormalHeadMax_le_log_card 2 (primeRelativeRadical 2 (commutator Original))
  rw [BinaryCarrierDerivedRadical16T1332.card_relative_radical] at h
  simpa only [show Nat.log 2 4 = 2 from by decide] using h

/-- The maximum is over all whole-original-group normal subgroups in
the actual intersection, not a list of candidate normal subgroups. -/
theorem normalHeadMax_intersection_le (N : Subgroup Original) [N.Normal]
    (hnotND : ¬N ≤ commutator Original) (hnotDN : ¬commutator Original ≤ N) :
    primeNormalHeadMax 2 (N ⊓ commutator Original) ≤
      max 2 (4 - Module.finrank (ZMod 2)
        (derivedCharactersVanishingOn 2 (N ⊓ commutator Original))) := by
  have hs : ∀ (M : Subgroup Original) [M.Normal],
      M ≤ primeRelativeRadical 2 (commutator Original) →
      Module.finrank (ZMod 2) (primeRelativeCharacters 2 M) ≤ 2 := by
    intro M _ hM
    exact (primeRelativeHead_le_normalHeadMax 2
      (primeRelativeRadical 2 (commutator Original)) M hM).trans normalHeadMax_radical_le_two
  have h := BinaryCarrierRadicalSaturation16T1332.certificate.normalHeadMax_le_max 2
    BinaryCarrierRadicalSaturation16T1332.nonempty_words 2 hs
    (N ⊓ commutator Original) inf_le_right (intersection_not_le_radical N hnotND hnotDN)
  rwa [intersection_head_eq N hnotND hnotDN] at h

theorem quotient_center_card (N : Subgroup Original) [N.Normal]
    (hnotND : ¬N ≤ commutator Original) (hnotDN : ¬commutator Original ≤ N) :
    Nat.card (Subgroup.center (Original ⧸ N)) =
      2 ^ (4 - Module.finrank (ZMod 2) (primeDerivedImage 2 N)) := by
  simpa only [horizontal_finrank] using
    quotientCenter_card_eq_pow_of_star_crossing 2 kernelIdentity
      BinaryCarrierExactOrder16T1332.original_isPGroup
      BinaryCarrierStarTransport16T1332.characterEquiv
      BinaryCarrierStarTransport16T1332.evaluationEquiv
      BinaryCarrierStarTransport16T1332.actual_form_eq_star
      N hnotDN (radical_le_intersection N hnotND hnotDN)

theorem quotient_derived_card (N : Subgroup Original) [N.Normal]
    (hnotND : ¬N ≤ commutator Original) (hnotDN : ¬commutator Original ≤ N) :
    Nat.card (commutator (Original ⧸ N)) =
      2 ^ Module.finrank (ZMod 2) (derivedCharactersVanishingOn 2 (N ⊓ commutator Original)) :=
  quotientCommutator_card_eq_pow_vanishing 2 N (radical_le_intersection N hnotND hnotDN)

end SymmetricSubgroupAsymptotics.BinaryCarrierStarCrossing16T1332
