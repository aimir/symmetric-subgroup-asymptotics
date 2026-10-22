import SymmetricSubgroupAsymptotics.CFSGOrthogonalBCoordinateFlip

/-! A literal product of the actual coordinate flips, without membership
or longest-Weyl hypotheses. Every firstFlips retains its exact original action. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalBCoordinateFlip
open CFSGOrthogonalBSerreMatrices
variable (K : Type) [Field K]

def spatialCoordinate {r : ℕ} : Fin r ⊕ Fin r → Fin r := Sum.elim id id

@[simp] theorem spatialCoordinate_swap {r : ℕ} (b : Fin r ⊕ Fin r) :
    spatialCoordinate b.swap = spatialCoordinate b := by cases b <;> rfl

theorem flip_spatial (r : ℕ) (j : Fin (r+1)) (b : Fin (r+1) ⊕ Fin (r+1)) :
    ((flip K r j).val : Mat K (r+1)) *ᵥ Pi.single (Sum.inl b) 1 =
      if spatialCoordinate b = j then -Pi.single (Sum.inl b.swap) 1 else Pi.single (Sum.inl b) 1 := by
  rw [flip_basis]
  cases b with
  | inl i =>
    by_cases hij : i = j
    · subst i; simp [spatialCoordinate, pos, neg, middle]
    · simp [spatialCoordinate, pos, neg, middle, hij, Equiv.swap_apply_def]
  | inr i =>
    by_cases hij : i = j
    · subst i; simp [spatialCoordinate, pos, neg, middle]
    · simp [spatialCoordinate, pos, neg, middle, hij, Equiv.swap_apply_def]

theorem flip_middle (r : ℕ) (j : Fin (r+1)) :
    ((flip K r j).val : Mat K (r+1)) *ᵥ Pi.single (middle (r+1)) 1 =
      -Pi.single (middle (r+1)) 1 := by
  simpa [pos, neg, middle, Equiv.swap_apply_def] using flip_basis K r j (middle (r+1))

def firstFlips (r : ℕ) : (k : ℕ) → k≤r+1 → elementaryRootGroup K (r+1)
  | 0,_ => 1
  | k+1,h => flip K r ⟨k,by omega⟩ * firstFlips r k (by omega)

theorem prefix_spatial (r k : ℕ) (hk : k≤r+1) (b : Fin (r+1) ⊕ Fin (r+1)) :
    ((firstFlips K r k hk).val : Mat K (r+1)) *ᵥ Pi.single (Sum.inl b) 1 =
      if (spatialCoordinate b).val < k then -Pi.single (Sum.inl b.swap) 1 else Pi.single (Sum.inl b) 1 := by
  induction k with
  | zero =>
    simp only [firstFlips, Subgroup.coe_one, Units.val_one, Matrix.one_mulVec,
      Nat.not_lt_zero, if_false]
  | succ k ih =>
    change (((flip K r ⟨k,by omega⟩).val : Mat K (r+1)) *
      ((firstFlips K r k (by omega)).val : Mat K (r+1))) *ᵥ _ = _
    rw [← Matrix.mulVec_mulVec, ih]
    by_cases hb : (spatialCoordinate b).val < k
    · have hne : spatialCoordinate b.swap≠(⟨k,by omega⟩:Fin (r+1)) := by
        intro h; have hh := congrArg Fin.val h; simp only [spatialCoordinate_swap] at hh; omega
      rw [if_pos hb, Matrix.mulVec_neg, flip_spatial, if_neg hne]
      rw [if_pos (by omega : (spatialCoordinate b).val < k+1)]
    · rw [if_neg hb, flip_spatial]
      by_cases he : (spatialCoordinate b).val = k
      · have heq : spatialCoordinate b=(⟨k,by omega⟩:Fin (r+1)) := Fin.ext he
        rw [if_pos heq, if_pos (by omega : (spatialCoordinate b).val < k+1)]
      · have hne : spatialCoordinate b≠(⟨k,by omega⟩:Fin (r+1)) := by
          intro h; exact he (congrArg Fin.val h)
        rw [if_neg hne, if_neg (by omega : ¬(spatialCoordinate b).val < k+1)]

theorem prefix_middle (r k : ℕ) (hk : k≤r+1) :
    ((firstFlips K r k hk).val : Mat K (r+1)) *ᵥ Pi.single (middle (r+1)) 1 =
      (-1:K)^k • Pi.single (middle (r+1)) 1 := by
  induction k with
  | zero =>
    simp only [firstFlips, Subgroup.coe_one, Units.val_one, Matrix.one_mulVec, pow_zero, one_smul]
  | succ k ih =>
    change (((flip K r ⟨k,by omega⟩).val : Mat K (r+1)) *
      ((firstFlips K r k (by omega)).val : Mat K (r+1))) *ᵥ _ = _
    rw [← Matrix.mulVec_mulVec, ih, Matrix.mulVec_smul, flip_middle]
    simp only [pow_succ, mul_neg, mul_one, neg_smul, smul_neg]

def opposition (r : ℕ) : elementaryRootGroup K (r+1) := firstFlips K r (r+1) le_rfl

theorem opposition_spatial (r : ℕ) (b : Fin (r+1) ⊕ Fin (r+1)) :
    ((opposition K r).val : Mat K (r+1)) *ᵥ Pi.single (Sum.inl b) 1 =
      -Pi.single (Sum.inl b.swap) 1 := by
  simpa [opposition, (spatialCoordinate b).isLt] using prefix_spatial K r (r+1) le_rfl b

theorem opposition_middle (r : ℕ) :
    ((opposition K r).val : Mat K (r+1)) *ᵥ Pi.single (middle (r+1)) 1 =
      (-1:K)^(r+1) • Pi.single (middle (r+1)) 1 := prefix_middle K r (r+1) le_rfl

end SymmetricSubgroupAsymptotics.CFSGOrthogonalBCoordinateFlip
