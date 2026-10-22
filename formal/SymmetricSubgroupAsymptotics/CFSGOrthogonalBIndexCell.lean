import SymmetricSubgroupAsymptotics.CFSGOrthogonalBIndexShears
import SymmetricSubgroupAsymptotics.CFSGOrthogonalBIndexSLCard
import SymmetricSubgroupAsymptotics.CFSGMatrixBlockCell

/-! A full-SL-middle opposite skew cell lies in the SAME actual odd B
elementary group. Its cardinal lower bound includes rank three; it is
not an order formula for a named orthogonal group. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalBIndexCell
open CFSGOrthogonalBSerreMatrices CFSGOrthogonalBIndexShears CFSGOrthogonalDIndexParameters
open CFSGMatrixShearUnits
variable (K : Type) [Field K]

abbrev CellParameters (r : ℕ) := Matrix.SpecialLinearGroup (Fin r) K ×
  (Parameters K r × Parameters K r)

def rawCell (r : ℕ) (p : CellParameters K r) :
    (Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)ˣ :=
  upper (alternating p.2.1) * CFSGOrthogonalDGenerationSLDouble.doubleHom K r p.1 *
    lower (alternating p.2.2)

theorem rawCell_val (r : ℕ) (p : CellParameters K r) :
    (rawCell K r p : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) =
      CFSGMatrixBlockCell.cell (Matrix.SpecialLinearGroup.toGL p.1)
        (alternating p.2.1) (alternating p.2.2) := rfl

theorem rawCell_injective (r : ℕ) : Function.Injective (rawCell K r) := by
  rintro ⟨A, p, q⟩ ⟨B, p', q'⟩ h
  have hm := congrArg (fun u : (Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)ˣ => u.val) h
  simp only [rawCell_val] at hm
  have he : (Matrix.SpecialLinearGroup.toGL A, (alternating p, alternating q)) =
      (Matrix.SpecialLinearGroup.toGL B, (alternating p', alternating q')) :=
    CFSGMatrixBlockCell.cell_injective hm
  have hA : A = B := Matrix.SpecialLinearGroup.toGL_injective (congrArg Prod.fst he)
  have hP : p = p' := alternating_injective (congrArg (Prod.fst ∘ Prod.snd) he)
  have hQ : q = q' := alternating_injective (congrArg (Prod.snd ∘ Prod.snd) he)
  exact Prod.ext hA (Prod.ext hP hQ)

def actualCell (h2 : (2 : K) ≠ 0) (s : ℕ) (p : CellParameters K (s + 1)) :
    elementaryRootGroup K (s + 1) :=
  ⟨extensionHom K (s + 1) (rawCell K (s + 1) p), by
    unfold rawCell
    rw [map_mul, map_mul]
    exact (elementaryRootGroup K (s + 1)).mul_mem
      ((elementaryRootGroup K (s + 1)).mul_mem (upper_alternating_mem K h2 s p.2.1)
        (CFSGOrthogonalBGenerationSLChain.doubleHom_range_le K (s + 1) ⟨p.1, rfl⟩))
      (lower_alternating_mem K h2 s p.2.2)⟩

theorem actualCell_unit (h2 : (2 : K) ≠ 0) (s : ℕ) (p : CellParameters K (s + 1)) :
    (actualCell K h2 s p).val = extensionHom K (s + 1) (rawCell K (s + 1) p) := rfl

theorem actualCell_injective (h2 : (2 : K) ≠ 0) (s : ℕ) :
    Function.Injective (actualCell K h2 s) := by
  intro p q hpq
  apply rawCell_injective K (s + 1)
  apply extensionHom_injective K (s + 1)
  have h := congrArg (fun u : elementaryRootGroup K (s + 1) => u.val) hpq
  simpa only [actualCell_unit] using h

theorem full_middle_cell_card_lower [Finite K] (h2 : (2 : K) ≠ 0) (s : ℕ) :
    Nat.card (Matrix.SpecialLinearGroup (Fin (s + 1)) K) *
      Nat.card K ^ ((s + 1) * s) ≤ Nat.card (elementaryRootGroup K (s + 1)) := by
  have h := Nat.card_le_card_of_injective (actualCell K h2 s) (actualCell_injective K h2 s)
  change Nat.card (CellParameters K (s + 1)) ≤ _ at h
  simp only [CellParameters, Nat.card_prod, parameters_card] at h
  rw [← pow_add, ← two_mul, entryIndex_card_twice] at h
  simpa only [Nat.add_sub_cancel] using h

theorem elementary_card_lower [Finite K] (h2 : (2 : K) ≠ 0) (s : ℕ) :
    Nat.card K ^ (2 * ((s + 1) * s)) * (Nat.card K - 1) ^ s ≤
      Nat.card (elementaryRootGroup K (s + 1)) := by
  have hSL := CFSGOrthogonalBIndexSLCard.specialLinear_card_lower K (s + 1) (by omega)
  have h := (Nat.mul_le_mul_right (Nat.card K ^ ((s + 1) * s)) hSL).trans
    (full_middle_cell_card_lower K h2 s)
  calc
    _ = (Nat.card K ^ ((s + 1) * s) * (Nat.card K - 1) ^ s) *
        Nat.card K ^ ((s + 1) * s) := by rw [two_mul, pow_add]; ring
    _ ≤ _ := by simpa only [Nat.add_sub_cancel] using h

end SymmetricSubgroupAsymptotics.CFSGOrthogonalBIndexCell
