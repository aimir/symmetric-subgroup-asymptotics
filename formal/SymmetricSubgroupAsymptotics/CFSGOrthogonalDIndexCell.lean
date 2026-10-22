import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexShears
import SymmetricSubgroupAsymptotics.CFSGMatrixBlockCell
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.GroupTheory.Index

/-! An actual opposite block cell in the literal D elementary group.
The middle is ANY actual SL block, not just a triangular subfamily; the
upper/lower alternating parameters are independently recovered from the
original four matrix blocks. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexCell
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDIndexParameters
open CFSGOrthogonalDIndexShears CFSGOrthogonalDGenerationSLDouble CFSGMatrixShearUnits
variable (K : Type) [Field K]

abbrev CellParameters (s : ℕ) := Matrix.SpecialLinearGroup (Fin (s + 4)) K ×
  (Parameters K (s + 4) × Parameters K (s + 4))

def actualCell (s : ℕ) (p : CellParameters K s) : elementaryRootGroup K (s + 4) :=
  ⟨upper (alternating p.2.1) * doubleHom K (s + 4) p.1 * lower (alternating p.2.2),
    (elementaryRootGroup K (s + 4)).mul_mem
      ((elementaryRootGroup K (s + 4)).mul_mem (upper_alternating_mem K s p.2.1)
        (doubleHom_range_le K (s + 4) ⟨p.1, rfl⟩))
      (lower_alternating_mem K s p.2.2)⟩

theorem actualCell_val (s : ℕ) (p : CellParameters K s) :
    ((actualCell K s p).val : Mat K (s + 4)) =
      CFSGMatrixBlockCell.cell (Matrix.SpecialLinearGroup.toGL p.1)
        (alternating p.2.1) (alternating p.2.2) := rfl

theorem actualCell_injective (s : ℕ) : Function.Injective (actualCell K s) := by
  rintro ⟨A, p, q⟩ ⟨B, p', q'⟩ h
  have hm := congrArg (fun u : elementaryRootGroup K (s + 4) => (u.val : Mat K (s + 4))) h
  simp only [actualCell_val] at hm
  have he : (Matrix.SpecialLinearGroup.toGL A, (alternating p, alternating q)) =
      (Matrix.SpecialLinearGroup.toGL B, (alternating p', alternating q')) :=
    CFSGMatrixBlockCell.cell_injective hm
  have hA : A = B := Matrix.SpecialLinearGroup.toGL_injective (congrArg Prod.fst he)
  have hP : p = p' := alternating_injective (congrArg (Prod.fst ∘ Prod.snd) he)
  have hQ : q = q' := alternating_injective (congrArg (Prod.snd ∘ Prod.snd) he)
  exact Prod.ext hA (Prod.ext hP hQ)

theorem full_middle_cell_card_lower [Finite K] (s : ℕ) :
    Nat.card (Matrix.SpecialLinearGroup (Fin (s + 4)) K) *
      Nat.card K ^ ((s + 4) * (s + 4 - 1)) ≤ Nat.card (elementaryRootGroup K (s + 4)) := by
  have h := Nat.card_le_card_of_injective (actualCell K s) (actualCell_injective K s)
  change Nat.card (Matrix.SpecialLinearGroup (Fin (s + 4)) K ×
    (Parameters K (s + 4) × Parameters K (s + 4))) ≤ _ at h
  simp only [Nat.card_prod, parameters_card] at h
  rw [← pow_add] at h
  have he : Nat.card (EntryIndex (s + 4)) + Nat.card (EntryIndex (s + 4)) =
      (s + 4) * (s + 4 - 1) := by have hh := entryIndex_card_twice (s + 4); omega
  simpa only [he] using h

def triangularCell (s : ℕ) (p : Parameters K (s + 4) ×
    (Parameters K (s + 4) × Parameters K (s + 4))) : elementaryRootGroup K (s + 4) :=
  actualCell K s (upperSL K (s + 4) p.1, p.2)

theorem triangularCell_injective (s : ℕ) : Function.Injective (triangularCell K s) := by
  intro p q h
  have he := actualCell_injective K s h
  have hhead : p.1 = q.1 := upperSL_injective K (s + 4)
    (congrArg (fun z : CellParameters K s => z.1) he)
  have htail : p.2 = q.2 := congrArg (fun z : CellParameters K s => z.2) he
  exact Prod.ext hhead htail

theorem triangular_cell_card_lower [Finite K] (s : ℕ) :
    Nat.card K ^ (3 * Nat.card (EntryIndex (s + 4))) ≤
      Nat.card (elementaryRootGroup K (s + 4)) := by
  have h := Nat.card_le_card_of_injective (triangularCell K s) (triangularCell_injective K s)
  change Nat.card (Parameters K (s + 4) ×
    (Parameters K (s + 4) × Parameters K (s + 4))) ≤ _ at h
  simp only [Nat.card_prod, parameters_card] at h
  rw [← pow_add, ← pow_add] at h
  have he : Nat.card (EntryIndex (s + 4)) +
      (Nat.card (EntryIndex (s + 4)) + Nat.card (EntryIndex (s + 4))) =
      3 * Nat.card (EntryIndex (s + 4)) := by omega
  simpa only [he] using h

theorem triangular_projective_cell_card_lower [Finite K] (s : ℕ) :
    Nat.card K ^ (3 * Nat.card (EntryIndex (s + 4))) ≤
      Nat.card (Subgroup.center (elementaryRootGroup K (s + 4))) *
        Nat.card (elementaryProjective K (s + 4)) :=
  (triangular_cell_card_lower K s).trans_eq
    (Subgroup.center (elementaryRootGroup K (s + 4))).card_mul_index.symm

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexCell
