import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexPrefixPerpendicular

/-! The only undetermined block of the intrinsic partial flag is its
last hyperbolic plane. Its actual induced matrix is diagonal or
anti-diagonal. This all-characteristic dichotomy retains, rather than
discards, the possible final-pair swap. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexMiddlePlane
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDIndexUnipotent
open CFSGOrthogonalDIndexPrefixNormalizer CFSGOrthogonalDIndexPrefixPerpendicular
open CFSGOrthogonalDIndexPolarForm CFSGOrthogonalDIndexQuadraticForm
variable (K : Type) [Field K]

def lastIndex (s : ℕ) : Fin (s + 4) := Fin.last (s + 3)
def middleCoordinate (s : ℕ) (side : Bool) : Index (s + 4) :=
  if side then Sum.inr (lastIndex s) else Sum.inl (lastIndex s)

theorem last_dotProduct (s : ℕ) (x y : Index (s + 4) → K)
    (hy : y ∈ positivePerpendicular K (s + 4) (s + 3)) :
    leftPart K x ⬝ᵥ rightPart K y =
      x (Sum.inl (lastIndex s)) * y (Sum.inr (lastIndex s)) := by
  apply Finset.sum_eq_single (lastIndex s)
  · intro j _ hj
    have hlt : j.val < s + 3 := by
      have hb := j.isLt
      have hn : j.val ≠ s + 3 := fun h => hj (Fin.ext h)
      omega
    change x (Sum.inl j) * y (Sum.inr j) = 0
    rw [hy j hlt, mul_zero]
  · intro h
    exact False.elim (h (Finset.mem_univ _))

theorem splitQ_on_last_perpendicular (s : ℕ) (x : Index (s + 4) → K)
    (hx : x ∈ positivePerpendicular K (s + 4) (s + 3)) :
    splitQ K x = x (Sum.inl (lastIndex s)) * x (Sum.inr (lastIndex s)) :=
  last_dotProduct K s x x hx

theorem polar_on_last_perpendicular (s : ℕ) (x y : Index (s + 4) → K)
    (hx : x ∈ positivePerpendicular K (s + 4) (s + 3))
    (hy : y ∈ positivePerpendicular K (s + 4) (s + 3)) :
    polar K x y = x (Sum.inl (lastIndex s)) * y (Sum.inr (lastIndex s)) +
      y (Sum.inl (lastIndex s)) * x (Sum.inr (lastIndex s)) := by
  rw [polar, last_dotProduct K s x y hy, last_dotProduct K s y x hx]

theorem middle_basis_perpendicular (s : ℕ) (side : Bool) :
    Pi.single (middleCoordinate s side) (1 : K) ∈
      positivePerpendicular K (s + 4) (s + 3) := by
  intro j hj
  have hn : j ≠ lastIndex s := by
    intro he
    have hv := congrArg Fin.val he
    change j.val = s + 3 at hv
    omega
  cases side <;> simp [middleCoordinate, Pi.single_apply, hn, Ne.symm hn]

theorem normalizer_middle_column_product (s : ℕ)
    (A : elementaryRootGroup K (s + 4))
    (hA : A ∈ Subgroup.normalizer
      (unipotent K (s + 4) : Set (elementaryRootGroup K (s + 4)))) (side : Bool) :
    (A.val : Mat K (s + 4)) (Sum.inl (lastIndex s)) (middleCoordinate s side) *
      (A.val : Mat K (s + 4)) (Sum.inr (lastIndex s)) (middleCoordinate s side) = 0 := by
  have hp := normalizer_preserves_positivePerpendicular K s A hA (s + 3) (by omega)
    _ (middle_basis_perpendicular K s side)
  have hq := elementary_preserves_splitQ K s A
    (Pi.single (middleCoordinate s side) 1)
  rw [splitQ_on_last_perpendicular K s _ hp, Matrix.mulVec_single_one] at hq
  have hz : splitQ K (Pi.single (middleCoordinate s side) (1 : K)) = 0 := by
    cases side <;> simp [middleCoordinate, splitQ, leftPart, rightPart, dotProduct,
      Pi.single_apply]
  exact hq.trans hz

theorem normalizer_middle_cross_product (s : ℕ)
    (A : elementaryRootGroup K (s + 4))
    (hA : A ∈ Subgroup.normalizer
      (unipotent K (s + 4) : Set (elementaryRootGroup K (s + 4)))) :
    (A.val : Mat K (s + 4)) (Sum.inl (lastIndex s)) (Sum.inl (lastIndex s)) *
        (A.val : Mat K (s + 4)) (Sum.inr (lastIndex s)) (Sum.inr (lastIndex s)) +
      (A.val : Mat K (s + 4)) (Sum.inl (lastIndex s)) (Sum.inr (lastIndex s)) *
        (A.val : Mat K (s + 4)) (Sum.inr (lastIndex s)) (Sum.inl (lastIndex s)) = 1 := by
  have hp := normalizer_preserves_positivePerpendicular K s A hA (s + 3) (by omega)
    _ (middle_basis_perpendicular K s false)
  have hn := normalizer_preserves_positivePerpendicular K s A hA (s + 3) (by omega)
    _ (middle_basis_perpendicular K s true)
  have h := elementary_preserves_polar K s A
    (Pi.single (middleCoordinate s false) 1) (Pi.single (middleCoordinate s true) 1)
  rw [polar_on_last_perpendicular K s _ _ hp hn, Matrix.mulVec_single_one,
    Matrix.mulVec_single_one] at h
  simpa [middleCoordinate, polar, leftPart, rightPart, dotProduct, Pi.single_apply,
    eq_comm] using h

theorem hyperbolic_plane_dichotomy (a b c d : K)
    (hac : a * c = 0) (hbd : b * d = 0) (hcross : a * d + b * c = 1) :
    (b = 0 ∧ c = 0 ∧ a * d = 1) ∨ (a = 0 ∧ d = 0 ∧ b * c = 1) := by
  by_cases ha : a = 0
  · have hbc : b * c = 1 := by simpa only [ha, zero_mul, zero_add] using hcross
    have hb : b ≠ 0 := by intro hb; simp only [hb, zero_mul] at hbc; exact zero_ne_one hbc
    exact Or.inr ⟨ha, (mul_eq_zero.mp hbd).resolve_left hb, hbc⟩
  · have hc : c = 0 := (mul_eq_zero.mp hac).resolve_left ha
    have had : a * d = 1 := by simpa only [hc, mul_zero, add_zero] using hcross
    have hd : d ≠ 0 := by intro hd; simp only [hd, mul_zero] at had; exact zero_ne_one had
    exact Or.inl ⟨(mul_eq_zero.mp hbd).resolve_right hd, hc, had⟩

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexMiddlePlane
