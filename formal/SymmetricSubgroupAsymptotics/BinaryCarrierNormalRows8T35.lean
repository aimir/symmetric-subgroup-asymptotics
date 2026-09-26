import SymmetricSubgroupAsymptotics.BinaryCarrierNormalProfiles8T35
import SymmetricSubgroupAsymptotics.BinaryCarrierWordHistory
import SymmetricSubgroupAsymptotics.BinaryCarrierStarEnvelope

/-! Exact carrier rows for every normal of the literal P=8T35 factor.
The complete original normal registry supplies the witness; repeated rows
retain distinct original axes. This binds the ten displayed P row values
without using their number as a subgroup count or asserting a weight bound. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.BinaryCarrierNormalRows8T35

open FullSubdirectGoursat BinaryCarrierNormal8T35

abbrev Original := BinaryCarrierNormalProfiles8T35.Original

def factor : BinaryCarrierWord.Factor where
  Carrier := Original
  group := inferInstance
  finite := inferInstance
  binary := IsPGroup.of_card (n := 7)
    (show Nat.card Original = 2 ^ 7 from BinaryMenuCayley8T35.exact_card)

def rowOfProfile (v : ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) : JointCapacityRow :=
  ⟨v.1, v.2.1, v.2.2.1, v.2.2.2.1, (v.2.2.2.2.1 : ℝ), (v.2.2.2.2.2 : ℝ)⟩

def registryRow (i : Fin 28) : JointCapacityRow :=
  rowOfProfile (BinaryCarrierNormalProfiles8T35.profileAt i)

theorem actualRow_eq_profile (N : NormalAxis Original) :
    BinaryCarrierWord.actualRow (A := factor) N =
      rowOfProfile (BinaryCarrierNormalProfiles8T35.profile N.1) := rfl

theorem actualRow_covered (N : NormalAxis Original) :
    ∃ i : Fin 28, originalKernel i = N.1 ∧
      BinaryCarrierWord.actualRow (A := factor) N = registryRow i := by
  obtain ⟨i, hi, hp⟩ := BinaryCarrierNormalProfiles8T35.complete_original_profile N.1
  exact ⟨i, hi, (actualRow_eq_profile N).trans (congrArg rowOfProfile hp)⟩

/-- The placement preserves the original displayed P block at indices31..40.
Different normal states may occupy the same numerical column. -/
def displayedIndex (i : Fin 28) : Fin 41 :=
  ![31,32,33,34,34,35,35,35,35,34,35,35,37,36,38,36,38,36,38,39,39,39,39,36,39,39,39,40] i

theorem registryRow_eq_displayed (i : Fin 28) :
    registryRow i = BinaryCarrierStarEnvelope.displayedRows (displayedIndex i) := by
  fin_cases i <;>
    norm_num [registryRow, rowOfProfile, BinaryCarrierNormalProfiles8T35.profileAt,
      headRank, orderLog, derivedHeadRank, radicalIndex, centerLog, derivedLog,
      displayedIndex, BinaryCarrierStarEnvelope.displayedRows]
  all_goals rfl

theorem displayedIndex_bounds (i : Fin 28) :
    31 ≤ (displayedIndex i).val ∧ (displayedIndex i).val < 41 := by
  fin_cases i <;> decide +kernel

theorem displayedIndex_scale (i : Fin 28) :
    BinaryCarrierStarEnvelope.displayedScale (displayedIndex i) = 1 := by
  fin_cases i <;> norm_num [displayedIndex, BinaryCarrierStarEnvelope.displayedScale]

/-- Coverage is an existential value assignment to EACH actual original axis,
not a replacement of normal subgroups by the ten displayed numerical rows. -/
theorem actualRow_displayed (N : NormalAxis Original) :
    ∃ i : Fin 28, originalKernel i = N.1 ∧
      BinaryCarrierWord.actualRow (A := factor) N =
        BinaryCarrierStarEnvelope.displayedRows (displayedIndex i) ∧
      BinaryCarrierStarEnvelope.displayedScale (displayedIndex i) = 1 := by
  obtain ⟨i, hi, hr⟩ := actualRow_covered N
  exact ⟨i, hi, hr.trans (registryRow_eq_displayed i), displayedIndex_scale i⟩

end SymmetricSubgroupAsymptotics.BinaryCarrierNormalRows8T35
