import SymmetricSubgroupAsymptotics.CFSGSymplecticInitialRootLines
import SymmetricSubgroupAsymptotics.CFSGDiagonalUnitRootAction

/-! Diagonal transport for the actual two initial C root lines. The
only coordinates needed are displayed explicitly, and all subgroup
statements concern the same original elementary group. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGSymplecticSerreMatrices

theorem initialShort_diagonal_conjugation (K : Type) [Field K] (r : ℕ) (hr : 0 < r)
    (T : elementaryRootGroup K (r + 1)) (d : Index (r + 1) → K)
    (hT : (T.val : Mat K (r + 1)) = Matrix.diagonal d) (l a : K)
    (hp : d (Sum.inl (⟨1, Nat.succ_lt_succ hr⟩ : Fin (r + 1))) = l * d (Sum.inl 0))
    (hn : d (Sum.inr (0 : Fin (r + 1))) =
      l * d (Sum.inr (⟨1, Nat.succ_lt_succ hr⟩ : Fin (r + 1)))) :
    T * initialShortRoot K r a * T⁻¹ = initialShortRoot K r (l * a) := by
  apply Subtype.ext
  exact CFSGDiagonalUnitRootAction.root_line_conjugation T.val
    (initialShortRoot K r a).val (initialShortRoot K r (l * a)).val
    d (initialShortMatrix K r hr) l a hT
    (initialShortRoot_coe K r hr a) (initialShortRoot_coe K r hr (l * a)) (by
      intro i j hX
      by_cases hpos : (Sum.inl (⟨1, Nat.succ_lt_succ hr⟩ : Fin (r + 1)) : Index (r + 1)) = i ∧
          (Sum.inl (0 : Fin (r + 1)) : Index (r + 1)) = j
      · rcases hpos with ⟨rfl, rfl⟩
        exact hp
      · by_cases hneg : (Sum.inr (0 : Fin (r + 1)) : Index (r + 1)) = i ∧
            (Sum.inr (⟨1, Nat.succ_lt_succ hr⟩ : Fin (r + 1)) : Index (r + 1)) = j
        · rcases hneg with ⟨rfl, rfl⟩
          exact hn
        · have hz : initialShortMatrix K r hr i j = 0 := by
            simp only [initialShortMatrix, Matrix.sub_apply, Matrix.single_apply,
              hpos, hneg, if_false, sub_self]
          exact (hX hz).elim)

theorem secondLong_diagonal_conjugation (K : Type) [Field K] (r : ℕ) (hr : 0 < r)
    (T : elementaryRootGroup K (r + 1)) (d : Index (r + 1) → K)
    (hT : (T.val : Mat K (r + 1)) = Matrix.diagonal d) (l a : K)
    (hp : d (Sum.inl (⟨1, Nat.succ_lt_succ hr⟩ : Fin (r + 1))) =
      l * d (Sum.inr (⟨1, Nat.succ_lt_succ hr⟩ : Fin (r + 1)))) :
    T * secondLongRoot K r a * T⁻¹ = secondLongRoot K r (l * a) := by
  let j : Fin (r + 1) := ⟨1, Nat.succ_lt_succ hr⟩
  have hroot : ∀ b : K, ((secondLongRoot K r b).val : Mat K (r + 1)) =
      1 + b • Matrix.single (Sum.inl j) (Sum.inr j) 1 := by
    intro b
    rw [secondLongRoot_coe K r hr]
    simp only [Matrix.transvection, Matrix.smul_single, smul_eq_mul, mul_one, j]
  apply Subtype.ext
  exact CFSGDiagonalUnitRootAction.root_line_conjugation T.val
    (secondLongRoot K r a).val (secondLongRoot K r (l * a)).val
    d (Matrix.single (Sum.inl j) (Sum.inr j) 1) l a hT (hroot a) (hroot (l * a)) (by
      intro i k hX
      by_cases h : (Sum.inl j : Index (r + 1)) = i ∧ (Sum.inr j : Index (r + 1)) = k
      · rcases h with ⟨rfl, rfl⟩
        exact hp
      · simp only [Matrix.single_apply, h, if_false, ne_eq, not_true_eq_false] at hX)

def initialDiagonal (K : Type) [Field K] (r : ℕ) (hr : 0 < r) (g : Kˣ) : Index (r + 1) → K :=
  fun x => coordinateTorusDiagonal K r 0 g x *
    coordinateTorusDiagonal K r (⟨1, Nat.succ_lt_succ hr⟩ : Fin (r + 1)) g x

theorem initialDiagonal_values (K : Type) [Field K] (r : ℕ) (hr : 0 < r) (g : Kˣ) :
    initialDiagonal K r hr g (Sum.inl 0) = (g : K) ∧
    initialDiagonal K r hr g (Sum.inl (⟨1, Nat.succ_lt_succ hr⟩ : Fin (r + 1))) = (g : K) ∧
    initialDiagonal K r hr g (Sum.inr 0) = (g : K)⁻¹ ∧
    initialDiagonal K r hr g (Sum.inr (⟨1, Nat.succ_lt_succ hr⟩ : Fin (r + 1))) = (g : K)⁻¹ := by
  have h01 : (0 : Fin (r + 1)) ≠ (⟨1, Nat.succ_lt_succ hr⟩ : Fin (r + 1)) := by
    intro h
    have hv := congrArg Fin.val h
    change 0 = 1 at hv
    omega
  simp [initialDiagonal, coordinateTorusDiagonal, h01, Ne.symm h01]

theorem initialTorus_short_conjugation (K : Type) [Field K] (r : ℕ) (hr : 0 < r)
    (g : Kˣ) (a : K) :
    initialTorus K r g * initialShortRoot K r a * (initialTorus K r g)⁻¹ =
      initialShortRoot K r a := by
  have hv := initialDiagonal_values K r hr g
  have h := initialShort_diagonal_conjugation K r hr (initialTorus K r g)
    (initialDiagonal K r hr g) (initialTorus_coe K r hr g) 1 a
    (by simp only [one_mul, hv.1, hv.2.1])
    (by simp only [one_mul, hv.2.2.1, hv.2.2.2])
  simpa only [one_mul] using h

theorem initialTorus_long_conjugation (K : Type) [Field K] (r : ℕ) (hr : 0 < r)
    (g : Kˣ) (a : K) :
    initialTorus K r g * secondLongRoot K r a * (initialTorus K r g)⁻¹ =
      secondLongRoot K r ((g : K) ^ 2 * a) := by
  have hv := initialDiagonal_values K r hr g
  apply secondLong_diagonal_conjugation K r hr (initialTorus K r g)
    (initialDiagonal K r hr g) (initialTorus_coe K r hr g)
  rw [hv.2.1, hv.2.2.2]
  field_simp

end SymmetricSubgroupAsymptotics.CFSGSymplecticSerreMatrices
