import SymmetricSubgroupAsymptotics.GeneratedCarrierNormal8T27.HeadMaxima
import SymmetricSubgroupAsymptotics.GeneratedCarrierNormal8T27.QuotientProfiles
import Mathlib.Data.Nat.Log

/-! All six exact carrier fields of every original J=8T27 normal.
A single complete-registry index retains the same actual subgroup in
every field. Equal numerical profiles do not identify original normals,
and this module makes no assertion about physical weights or owners. -/
set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics.BinaryCarrierNormalProfiles8T27

open BinaryCarrierNormal8T27

abbrev Original := BinaryCarrierNormal8T27.Original

/-- The six actual fields, with both character heads taken under the
whole original ambient conjugation and m ranging over its original normals. -/
def profile (N : Subgroup Original) [N.Normal] : ℕ × ℕ × ℕ × ℕ × ℕ × ℕ :=
  (Module.finrank (ZMod 2) (primeRelativeCharacters 2 N), Nat.log 2 (Nat.card N),
    primeNormalHeadMax 2 (N ⊓ commutator Original),
    Module.finrank (ZMod 2) (primeRelativeCharacters 2 (primeRelativeRadical 2 N)),
    Nat.log 2 (Nat.card (Subgroup.center (Original ⧸ N))),
    Nat.log 2 (Nat.card (commutator (Original ⧸ N))))

/-- These values come from proved subgroup, radical, containment and quotient
certificates; this definition accepts no stored six-field profile. -/
def profileAt (i : Fin 13) : ℕ × ℕ × ℕ × ℕ × ℕ × ℕ :=
  (headRank i, orderLog i, derivedHeadRank i,
    headRank (radicalIndex i), centerLog i, derivedLog i)

theorem original_profile_eq (i : Fin 13) :
    profile (originalKernel i) = profileAt i := by
  unfold profile profileAt
  rw [original_head_eq i, original_card i, original_derived_head_eq i,
    original_radical_head_eq i, original_quotient_center_card i,
    original_quotient_derived_card i]
  simp only [Nat.log_pow (by decide : 1 < (2 : ℕ))]

/-- One registry witness simultaneously binds all six original fields. -/
theorem complete_original_fields (N : Subgroup Original) [N.Normal] :
    ∃ i : Fin 13, originalKernel i = N ∧
      Module.finrank (ZMod 2) (primeRelativeCharacters 2 N) = headRank i ∧
      Nat.card N = 2 ^ orderLog i ∧
      primeNormalHeadMax 2 (N ⊓ commutator Original) = derivedHeadRank i ∧
      Module.finrank (ZMod 2) (primeRelativeCharacters 2 (primeRelativeRadical 2 N)) =
        headRank (radicalIndex i) ∧
      Nat.card (Subgroup.center (Original ⧸ N)) = 2 ^ centerLog i ∧
      Nat.card (commutator (Original ⧸ N)) = 2 ^ derivedLog i := by
  obtain ⟨i, hi⟩ := complete_original N
  change originalKernel i = N at hi
  subst N
  exact ⟨i, rfl, original_head_eq i, original_card i, original_derived_head_eq i,
    original_radical_head_eq i, original_quotient_center_card i,
    original_quotient_derived_card i⟩

theorem complete_original_profile (N : Subgroup Original) [N.Normal] :
    ∃ i : Fin 13, originalKernel i = N ∧ profile N = profileAt i := by
  obtain ⟨i, hi⟩ := complete_original N
  change originalKernel i = N at hi
  subst N
  exact ⟨i, rfl, original_profile_eq i⟩

end SymmetricSubgroupAsymptotics.BinaryCarrierNormalProfiles8T27
