import SymmetricSubgroupAsymptotics.BinaryCarrierNormalProfiles8T27
import SymmetricSubgroupAsymptotics.BinaryCarrierWordHistory
import SymmetricSubgroupAsymptotics.BinaryCarrierStarEnvelope

/-! Exact carrier rows for every normal of the literal J=8T27 factor.
The complete original normal registry supplies the witness; repeated rows
retain distinct original axes. This binds the ten displayed J row values
without using their number as a subgroup count or asserting a weight bound. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.BinaryCarrierNormalRows8T27

open FullSubdirectGoursat BinaryCarrierNormal8T27

abbrev Original := BinaryCarrierNormalProfiles8T27.Original

def factor : BinaryCarrierWord.Factor where
  Carrier := Original
  group := inferInstance
  finite := inferInstance
  binary := IsPGroup.of_card (n := 6)
    (show Nat.card Original = 2 ^ 6 from BinaryMenuCayley8T27.exact_card)

def rowOfProfile (v : ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) : JointCapacityRow :=
  ⟨v.1, v.2.1, v.2.2.1, v.2.2.2.1, (v.2.2.2.2.1 : ℝ), (v.2.2.2.2.2 : ℝ)⟩

def registryRow (i : Fin 13) : JointCapacityRow :=
  rowOfProfile (BinaryCarrierNormalProfiles8T27.profileAt i)

theorem actualRow_eq_profile (N : NormalAxis Original) :
    BinaryCarrierWord.actualRow (A := factor) N =
      rowOfProfile (BinaryCarrierNormalProfiles8T27.profile N.1) := rfl

theorem actualRow_covered (N : NormalAxis Original) :
    ∃ i : Fin 13, originalKernel i = N.1 ∧
      BinaryCarrierWord.actualRow (A := factor) N = registryRow i := by
  obtain ⟨i, hi, hp⟩ := BinaryCarrierNormalProfiles8T27.complete_original_profile N.1
  exact ⟨i, hi, (actualRow_eq_profile N).trans (congrArg rowOfProfile hp)⟩

/-- The placement preserves the original displayed J block at indices21..30.
Different normal states may occupy the same numerical column. -/
def displayedIndex (i : Fin 13) : Fin 41 :=
  ![21,22,23,24,25,26,26,24,28,27,29,27,30] i

theorem registryRow_eq_displayed (i : Fin 13) :
    registryRow i = BinaryCarrierStarEnvelope.displayedRows (displayedIndex i) := by
  fin_cases i <;>
    norm_num [registryRow, rowOfProfile, BinaryCarrierNormalProfiles8T27.profileAt,
      headRank, orderLog, derivedHeadRank, radicalIndex, centerLog, derivedLog,
      displayedIndex, BinaryCarrierStarEnvelope.displayedRows]
  all_goals rfl

theorem displayedIndex_bounds (i : Fin 13) :
    21 ≤ (displayedIndex i).val ∧ (displayedIndex i).val < 31 := by
  fin_cases i <;> decide +kernel

theorem displayedIndex_scale (i : Fin 13) :
    BinaryCarrierStarEnvelope.displayedScale (displayedIndex i) = 1 := by
  fin_cases i <;> norm_num [displayedIndex, BinaryCarrierStarEnvelope.displayedScale]

/-- Coverage is an existential value assignment to EACH actual original axis,
not a replacement of normal subgroups by the ten displayed numerical rows. -/
theorem actualRow_displayed (N : NormalAxis Original) :
    ∃ i : Fin 13, originalKernel i = N.1 ∧
      BinaryCarrierWord.actualRow (A := factor) N =
        BinaryCarrierStarEnvelope.displayedRows (displayedIndex i) ∧
      BinaryCarrierStarEnvelope.displayedScale (displayedIndex i) = 1 := by
  obtain ⟨i, hi, hr⟩ := actualRow_covered N
  exact ⟨i, hi, hr.trans (registryRow_eq_displayed i), displayedIndex_scale i⟩

end SymmetricSubgroupAsymptotics.BinaryCarrierNormalRows8T27
