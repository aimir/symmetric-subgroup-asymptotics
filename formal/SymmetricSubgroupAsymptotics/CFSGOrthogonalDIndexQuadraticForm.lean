import SymmetricSubgroupAsymptotics.CFSGOrthogonalDGenerationPureRootCoverage

/-! The SAME literal elementary D matrices preserve the split
quadratic form in every characteristic. This is stronger than polar
bilinear-form preservation in characteristic two and excludes spurious
single-diagonal shears in later intrinsic root recognition. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexQuadraticForm
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDBinaryElements
open CFSGOrthogonalDGenerationForkTorus CFSGOrthogonalDGenerationRootArrays
open CFSGOrthogonalDGenerationInitialRootMatrices CFSGOrthogonalDGenerationPureRootCoverage
variable (K : Type) [Field K]

abbrev leftPart {r : ℕ} (x : Index r → K) : Fin r → K := x ∘ Sum.inl
abbrev rightPart {r : ℕ} (x : Index r → K) : Fin r → K := x ∘ Sum.inr

def splitQ {r : ℕ} (x : Index r → K) : K := leftPart K x ⬝ᵥ rightPart K x

private theorem single_mulVec {r : ℕ} (i j : Index r) (a : K) (x : Index r → K) :
    Matrix.single i j a *ᵥ x = Pi.single i (a * x j) := by
  funext k
  by_cases hk : k = i
  · subst k
    simp [Matrix.mulVec, dotProduct, Matrix.single_apply, Pi.single_apply]
  · have hik : i ≠ k := Ne.symm hk
    simp [Matrix.mulVec, dotProduct, Matrix.single_apply, Pi.single_apply, hk, hik]

private theorem chain_left {r : ℕ} (i j : Fin r) (a : K) (x : Index r → K) :
    leftPart K (chainArray i j a *ᵥ x) =
      leftPart K x + Pi.single i (a * leftPart K x j) := by
  funext k
  simp [leftPart, chainArray, Matrix.add_mulVec, Matrix.sub_mulVec, single_mulVec,
    Pi.single_apply]

private theorem chain_right {r : ℕ} (i j : Fin r) (a : K) (x : Index r → K) :
    rightPart K (chainArray i j a *ᵥ x) =
      rightPart K x - Pi.single j (a * rightPart K x i) := by
  funext k
  simp [rightPart, chainArray, Matrix.add_mulVec, Matrix.sub_mulVec, single_mulVec,
    Pi.single_apply]

theorem chain_preserves_splitQ {r : ℕ} (i j : Fin r) (hij : i ≠ j) (a : K) (x : Index r → K) :
    splitQ K (chainArray i j a *ᵥ x) = splitQ K x := by
  rw [splitQ, chain_left, chain_right]
  simp only [add_dotProduct, dotProduct_sub, single_dotProduct, dotProduct_single,
    Pi.add_apply, Pi.single_apply, if_neg (Ne.symm hij), add_zero]
  unfold splitQ
  ring

private theorem plus_left {r : ℕ} (i j : Fin r) (a : K) (x : Index r → K) :
    leftPart K (plusArray i j a *ᵥ x) =
      leftPart K x + Pi.single i (a * rightPart K x j) - Pi.single j (a * rightPart K x i) := by
  funext k
  simp [leftPart, rightPart, plusArray, Matrix.add_mulVec, Matrix.sub_mulVec,
    single_mulVec, Pi.single_apply]

private theorem plus_right {r : ℕ} (i j : Fin r) (a : K) (x : Index r → K) :
    rightPart K (plusArray i j a *ᵥ x) = rightPart K x := by
  funext k
  simp [rightPart, plusArray, Matrix.add_mulVec, Matrix.sub_mulVec, single_mulVec]

theorem plus_preserves_splitQ {r : ℕ} (i j : Fin r) (a : K) (x : Index r → K) :
    splitQ K (plusArray i j a *ᵥ x) = splitQ K x := by
  rw [splitQ, plus_left, plus_right, sub_dotProduct, add_dotProduct]
  simp only [single_dotProduct]
  unfold splitQ
  ring

private theorem minus_left {r : ℕ} (i j : Fin r) (a : K) (x : Index r → K) :
    leftPart K (minusArray i j a *ᵥ x) = leftPart K x := by
  funext k
  simp [leftPart, minusArray, plusArray, Matrix.transpose_add, Matrix.transpose_sub,
    Matrix.transpose_one, Matrix.transpose_single, Matrix.add_mulVec, Matrix.sub_mulVec,
    single_mulVec]

private theorem minus_right {r : ℕ} (i j : Fin r) (a : K) (x : Index r → K) :
    rightPart K (minusArray i j a *ᵥ x) =
      rightPart K x + Pi.single j (a * leftPart K x i) - Pi.single i (a * leftPart K x j) := by
  funext k
  simp [leftPart, rightPart, minusArray, plusArray, Matrix.transpose_add, Matrix.transpose_sub,
    Matrix.transpose_one, Matrix.transpose_single, Matrix.add_mulVec, Matrix.sub_mulVec,
    single_mulVec, Pi.single_apply]

theorem minus_preserves_splitQ {r : ℕ} (i j : Fin r) (a : K) (x : Index r → K) :
    splitQ K (minusArray i j a *ᵥ x) = splitQ K x := by
  rw [splitQ, minus_left, minus_right, dotProduct_sub, dotProduct_add]
  simp only [dotProduct_single]
  unfold splitQ
  ring

theorem root_preserves_splitQ (s : ℕ) (neg : Bool) (i : Fin (s + 4)) (a : K)
    (x : Index (s + 4) → K) :
    splitQ K ((rootTransvection K (s + 4) neg i a : Mat K (s + 4)) *ᵥ x) = splitQ K x := by
  by_cases hi : i.val + 1 < s + 4
  · have hij : i ≠ (⟨i.val + 1, hi⟩ : Fin (s + 4)) := by
      intro he
      have hv := congrArg Fin.val he
      change i.val = i.val + 1 at hv
      omega
    change splitQ K (((rootElement K (s + 4) neg i a).val : Mat K (s + 4)) *ᵥ x) = _
    rw [chain_root_array K s neg i hi a]
    cases neg
    · exact chain_preserves_splitQ K i _ hij a x
    · exact chain_preserves_splitQ K _ i (Ne.symm hij) a x
  · have he : i = last (s + 2) := by
      apply Fin.ext
      have hb := i.isLt
      change i.val = s + 3
      omega
    subst i
    change splitQ K (((rootElement K (s + 4) neg (last (s + 2)) a).val : Mat K (s + 4)) *ᵥ x) = _
    rw [forkRoot_coe K s neg a]
    cases neg
    · exact plus_preserves_splitQ K (pen (s + 2)) (last (s + 2)) a x
    · simpa only [minusArray, plusArray, Matrix.transpose_add, Matrix.transpose_sub,
        Matrix.transpose_one, Matrix.transpose_single] using
        minus_preserves_splitQ K (pen (s + 2)) (last (s + 2)) a x

def quadraticPreserving (r : ℕ) : Subgroup (Mat K r)ˣ where
  carrier := {u | ∀ x : Index r → K, splitQ K ((u : Mat K r) *ᵥ x) = splitQ K x}
  one_mem' := by intro x; simp
  mul_mem' := by
    intro u v hu hv x
    change splitQ K (((u : Mat K r) * (v : Mat K r)) *ᵥ x) = _
    rw [← Matrix.mulVec_mulVec, hu, hv]
  inv_mem' := by
    intro u hu x
    have h := hu ((↑(u⁻¹) : Mat K r) *ᵥ x)
    rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec] at h
    exact h.symm

theorem elementary_le_quadraticPreserving (s : ℕ) :
    elementaryRootGroup K (s + 4) ≤ quadraticPreserving K (s + 4) := by
  apply (Subgroup.closure_le _).mpr
  rintro u ⟨neg, i, a, rfl⟩
  exact root_preserves_splitQ K s neg i a

theorem elementary_preserves_splitQ (s : ℕ) (u : elementaryRootGroup K (s + 4))
    (x : Index (s + 4) → K) : splitQ K ((u.val : Mat K (s + 4)) *ᵥ x) = splitQ K x :=
  elementary_le_quadraticPreserving K s u.property x

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexQuadraticForm
