import SymmetricSubgroupAsymptotics.CFSGSymplecticStabilizerCoordinates

/-! The literal hyperbolic-pair stabilizer restricts faithfully to the
remaining coordinates. The restricted matrix has an explicit inverse:
the same restriction of the original inverse. -/
set_option autoImplicit false
noncomputable section
open scoped Matrix BigOperators
namespace SymmetricSubgroupAsymptotics.CFSGSymplecticStabilizerCoordinates
open CFSGSymplecticSerreMatrices
variable {K : Type} [Field K]

def FixesFirstPair (r : ℕ) (A : Mat K (r + 1)) : Prop :=
  A *ᵥ Pi.single (Sum.inl 0) 1 = Pi.single (Sum.inl 0) 1 ∧
  A *ᵥ Pi.single (Sum.inr 0) 1 = Pi.single (Sum.inr 0) 1

theorem tailMatrix_mul (r : ℕ) (A B : Mat K (r + 1)) (hA : FixesFirstPair r A) :
    tailMatrix r (A * B) = tailMatrix r A * tailMatrix r B := by
  ext i j
  have hp : A (tailIndex r i) (Sum.inl 0) = 0 := by
    have h := fixed_basis_column (r + 1) A (Sum.inl 0) hA.1 (tailIndex r i)
    cases i <;> simpa [tailIndex, Pi.single_apply] using h
  have hn : A (tailIndex r i) (Sum.inr 0) = 0 := by
    have h := fixed_basis_column (r + 1) A (Sum.inr 0) hA.2 (tailIndex r i)
    cases i <;> simpa [tailIndex, Pi.single_apply] using h
  simp only [tailIndex] at hp hn
  simp only [tailMatrix, Matrix.submatrix_apply, Matrix.mul_apply,
    Fintype.sum_sum_type, Fin.sum_univ_succ, tailIndex, Sum.map_inl, Sum.map_inr,
    hp, hn, zero_mul, zero_add]

@[simp] theorem tailMatrix_one (r : ℕ) : tailMatrix r (1 : Mat K (r + 1)) = 1 := by
  ext i j
  cases i <;> cases j <;> simp [tailMatrix, tailIndex, Matrix.one_apply]

theorem fixesFirstPair_inv (r : ℕ) (u : (Mat K (r + 1))ˣ)
    (hu : FixesFirstPair r (u : Mat K (r + 1))) :
    FixesFirstPair r (↑(u⁻¹) : Mat K (r + 1)) := by
  have hfix (v : Index (r + 1) → K) (hv : (u : Mat K (r + 1)) *ᵥ v = v) :
      (↑(u⁻¹) : Mat K (r + 1)) *ᵥ v = v := by
    calc
      _ = (↑(u⁻¹) : Mat K (r + 1)) *ᵥ ((u : Mat K (r + 1)) *ᵥ v) := by rw [hv]
      _ = ((↑(u⁻¹) : Mat K (r + 1)) * (u : Mat K (r + 1))) *ᵥ v :=
        Matrix.mulVec_mulVec _ _ _
      _ = v := by rw [Units.inv_mul, Matrix.one_mulVec]
  exact ⟨hfix _ hu.1, hfix _ hu.2⟩

def tailUnits (r : ℕ) (u : (Mat K (r + 1))ˣ)
    (hu : FixesFirstPair r (u : Mat K (r + 1))) : (Mat K r)ˣ where
  val := tailMatrix r u.val
  inv := tailMatrix r (u⁻¹).val
  val_inv := by
    rw [← tailMatrix_mul r _ _ hu,
      show (u : Mat K (r + 1)) * (↑(u⁻¹) : Mat K (r + 1)) = 1 from u.val_inv,
      tailMatrix_one]
  inv_val := by
    rw [← tailMatrix_mul r _ _ (fixesFirstPair_inv r u hu),
      show (↑(u⁻¹) : Mat K (r + 1)) * (u : Mat K (r + 1)) = 1 from u.inv_val,
      tailMatrix_one]

theorem tailUnits_preserves_pairing (r : ℕ) (u : (Mat K (r + 1))ˣ)
    (hu : FixesFirstPair r (u : Mat K (r + 1)))
    (hA : PreservesPairing (r + 1) (u : Mat K (r + 1))) :
    PreservesPairing r (tailUnits r u hu : Mat K r) :=
  tailMatrix_preserves_pairing r (u : Mat K (r + 1)) hA hu.1 hu.2

theorem index_head_or_tail (r : ℕ) (i : Index (r + 1)) :
    i = Sum.inl 0 ∨ i = Sum.inr 0 ∨ ∃ j, i = tailIndex r j := by
  cases i with
  | inl i =>
    refine Fin.cases ?_ (fun j => ?_) i
    · exact Or.inl rfl
    · exact Or.inr (Or.inr ⟨Sum.inl j, rfl⟩)
  | inr i =>
    refine Fin.cases ?_ (fun j => ?_) i
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr ⟨Sum.inr j, rfl⟩)

theorem eq_of_same_tail (r : ℕ) (A B : Mat K (r + 1))
    (hA : PreservesPairing (r + 1) A) (hB : PreservesPairing (r + 1) B)
    (ha : FixesFirstPair r A) (hb : FixesFirstPair r B)
    (h : tailMatrix r A = tailMatrix r B) : A = B := by
  ext i j
  rcases index_head_or_tail r i with rfl | rfl | ⟨i, rfl⟩
  · exact (fixed_negative_basis_row (r + 1) A hA 0 ha.2 j).trans
      (fixed_negative_basis_row (r + 1) B hB 0 hb.2 j).symm
  · exact (fixed_positive_basis_row (r + 1) A hA 0 ha.1 j).trans
      (fixed_positive_basis_row (r + 1) B hB 0 hb.1 j).symm
  · rcases index_head_or_tail r j with rfl | rfl | ⟨j, rfl⟩
    · exact (fixed_basis_column (r + 1) A _ ha.1 _).trans
        (fixed_basis_column (r + 1) B _ hb.1 _).symm
    · exact (fixed_basis_column (r + 1) A _ ha.2 _).trans
        (fixed_basis_column (r + 1) B _ hb.2 _).symm
    · exact congrArg (fun M : Mat K r => M i j) h

end SymmetricSubgroupAsymptotics.CFSGSymplecticStabilizerCoordinates
