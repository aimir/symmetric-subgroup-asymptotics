import SymmetricSubgroupAsymptotics.CFSGSymplecticSymmetricShearMembership
import SymmetricSubgroupAsymptotics.CFSGSymplecticBorelCellMiddle
import SymmetricSubgroupAsymptotics.CFSGSymmetricMatrixCardinality
import SymmetricSubgroupAsymptotics.CFSGSymplecticElementaryProjectiveCenter
import Mathlib.GroupTheory.Index

/-! A single literal opposite cell inside the original elementary C
group: two arbitrary symmetric shears and a two-coordinate SL Borel.
Its parameters are recovered by the same block-cell injection. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGSymplecticSerreMatrices
open CFSGSymmetricMatrixCardinality CFSGMatrixShearUnits
variable (K : Type) [Field K]

abbrev AugmentedCellParameters (r : ℕ) :=
  (Kˣ × K) × (SymmetricMatrix K (Fin (r + 1)) × SymmetricMatrix K (Fin (r + 1)))

def augmentedCell (r : ℕ) (hr : 0 < r) (p : AugmentedCellParameters K r) :
    elementaryRootGroup K (r + 1) :=
  ⟨upper p.2.1.val * CFSGMatrixDiagonalBlockLift.lift
      (borelCellMiddle K r hr p.1.1 p.1.2) * lower p.2.2.val,
    (elementaryRootGroup K (r + 1)).mul_mem
      ((elementaryRootGroup K (r + 1)).mul_mem
        (symmetric_upper_mem K r hr p.2.1.val (transpose_eq p.2.1))
        (borelCellMiddle_lift_mem K r hr p.1.1 p.1.2))
      (symmetric_lower_mem K r hr p.2.2.val (transpose_eq p.2.2))⟩

theorem augmentedCell_val (r : ℕ) (hr : 0 < r) (p : AugmentedCellParameters K r) :
    ((augmentedCell K r hr p).val : Mat K (r + 1)) =
      CFSGMatrixBlockCell.cell (borelCellMiddle K r hr p.1.1 p.1.2) p.2.1.val p.2.2.val := rfl

theorem augmentedCell_injective (r : ℕ) (hr : 0 < r) :
    Function.Injective (augmentedCell K r hr) := by
  rintro ⟨⟨g, t⟩, S, T⟩ ⟨⟨g', t'⟩, S', T'⟩ h
  have hm := congrArg (fun u : elementaryRootGroup K (r + 1) => (u.val : Mat K (r + 1))) h
  simp only [augmentedCell_val] at hm
  have he : (borelCellMiddle K r hr g t, (S.val, T.val)) =
      (borelCellMiddle K r hr g' t', (S'.val, T'.val)) :=
    CFSGMatrixBlockCell.cell_injective hm
  have hgt : (g, t) = (g', t') := borelCellMiddle_injective K r hr (congrArg Prod.fst he)
  have hS := congrArg (fun p : (Matrix (Fin (r + 1)) (Fin (r + 1)) K)ˣ ×
      (Matrix (Fin (r + 1)) (Fin (r + 1)) K × Matrix (Fin (r + 1)) (Fin (r + 1)) K) => p.2.1) he
  have hT := congrArg (fun p : (Matrix (Fin (r + 1)) (Fin (r + 1)) K)ˣ ×
      (Matrix (Fin (r + 1)) (Fin (r + 1)) K × Matrix (Fin (r + 1)) (Fin (r + 1)) K) => p.2.2) he
  exact Prod.ext hgt (Prod.ext (Subtype.ext hS) (Subtype.ext hT))

theorem augmentedCell_card_lower [Finite K] (r : ℕ) (hr : 0 < r) :
    Nat.card K ^ ((r + 1) * (r + 2) + 1) * (Nat.card K - 1) ≤
      Nat.card (elementaryRootGroup K (r + 1)) := by
  have h := Nat.card_le_card_of_injective (augmentedCell K r hr) (augmentedCell_injective K r hr)
  change Nat.card ((Kˣ × K) ×
    (SymmetricMatrix K (Fin (r + 1)) × SymmetricMatrix K (Fin (r + 1)))) ≤ _ at h
  rw [Nat.card_prod, Nat.card_prod, symmetricMatrix_pair_card, Nat.card_units] at h
  convert h using 1 <;> ring

theorem augmentedCell_projective_card_lower [Finite K] (r : ℕ) (hr : 0 < r) :
    Nat.card K ^ ((r + 1) * (r + 2) + 1) * (Nat.card K - 1) ≤
      Nat.card (Subgroup.center (elementaryRootGroup K (r + 1))) *
        Nat.card (elementaryProjective K (r + 1)) := by
  exact (augmentedCell_card_lower K r hr).trans_eq
    (Subgroup.center (elementaryRootGroup K (r + 1))).card_mul_index.symm

end SymmetricSubgroupAsymptotics.CFSGSymplecticSerreMatrices
