import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexParameters
import SymmetricSubgroupAsymptotics.CFSGOrthogonalBGenerationLongElements
import SymmetricSubgroupAsymptotics.CFSGOrthogonalBGenerationSLChain
import SymmetricSubgroupAsymptotics.CFSGMatrixShearUnits

/-! The SAME actual odd B group contains every alternating upper/lower
block shear on its paired coordinates, with the middle coordinate fixed.
Membership comes from explicit short-root commutators, not a D-model
identification or an assumed full orthogonal group. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped BigOperators Matrix
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalBIndexShears
open CFSGOrthogonalBSerreMatrices CFSGOrthogonalBGenerationLongElements
open CFSGOrthogonalBGenerationShortArrays CFSGOrthogonalBGenerationShortCommutator
open CFSGOrthogonalDIndexParameters CFSGMatrixShearUnits CFSGMatrixIdentityExtension
variable (K : Type) [Field K]

def extensionHom (r : ℕ) :
    (Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)ˣ →* (Mat K r)ˣ :=
  Units.map (extend K (Fin r ⊕ Fin r) Unit)

theorem extensionHom_injective (r : ℕ) : Function.Injective (extensionHom K r) := by
  intro A B h
  apply Units.ext
  ext i j
  have he := congrArg (fun u : (Mat K r)ˣ =>
    (u : Mat K r) (Sum.inl i) (Sum.inl j)) h
  simpa [extensionHom, extend, Matrix.fromBlocks] using he

private theorem upper_pair_mem (h2 : (2 : K) ≠ 0) (s : ℕ)
    (i j : Fin (s + 1)) (hij : i ≠ j) (a : K) :
    extensionHom K (s + 1) (upper (Matrix.single i j a - Matrix.single j i a)) ∈
      elementaryRootGroup K (s + 1) := by
  let u := longRootElement K s (Sum.inl i) (Sum.inl j) a
  have hu : (u.val : Mat K (s + 1)) = 1 + a • longArray K (s + 1) (Sum.inl i) (Sum.inl j) :=
    longRootElement_val K h2 s _ _ (by simpa using hij) (by intro h; cases h) a
  have he : extensionHom K (s + 1) (upper (Matrix.single i j a - Matrix.single j i a)) = u.val := by
    apply Units.ext
    rw [hu]
    ext x y
    rcases x with ((x | x) | ⟨⟩) <;> rcases y with ((y | y) | ⟨⟩) <;>
      simp [extensionHom, extend, upper, Matrix.fromBlocks, longArray, paired,
        Matrix.one_apply, Matrix.single_apply] <;>
      simp only [smul_eq_mul, mul_sub, mul_ite, mul_one, mul_zero]
  rw [he]
  exact u.property

private theorem lower_pair_mem (h2 : (2 : K) ≠ 0) (s : ℕ)
    (i j : Fin (s + 1)) (hij : i ≠ j) (a : K) :
    extensionHom K (s + 1) (lower (Matrix.single i j a - Matrix.single j i a)) ∈
      elementaryRootGroup K (s + 1) := by
  let u := longRootElement K s (Sum.inr i) (Sum.inr j) a
  have hu : (u.val : Mat K (s + 1)) = 1 + a • longArray K (s + 1) (Sum.inr i) (Sum.inr j) :=
    longRootElement_val K h2 s _ _ (by simpa using hij) (by intro h; cases h) a
  have he : extensionHom K (s + 1) (lower (Matrix.single i j a - Matrix.single j i a)) = u.val := by
    apply Units.ext
    rw [hu]
    ext x y
    rcases x with ((x | x) | ⟨⟩) <;> rcases y with ((y | y) | ⟨⟩) <;>
      simp [extensionHom, extend, lower, Matrix.fromBlocks, longArray, paired,
        Matrix.one_apply, Matrix.single_apply] <;>
      simp only [smul_eq_mul, mul_sub, mul_ite, mul_one, mul_zero]
  rw [he]
  exact u.property

private theorem alternating_sum {r : ℕ} (p : Parameters K r) :
    alternating p = ∑ i, ∑ j,
      (Matrix.single i j (strictUpper p i j) - Matrix.single j i (strictUpper p i j)) := by
  simp only [Finset.sum_sub_distrib]
  rw [Matrix.sum_sum_single]
  unfold alternating
  congr 1
  have ht := congrArg Matrix.transpose (Matrix.sum_sum_single (strictUpper p))
  simpa only [Matrix.transpose_sum, Matrix.transpose_single] using ht.symm

theorem upper_alternating_mem (h2 : (2 : K) ≠ 0) (s : ℕ) (p : Parameters K (s + 1)) :
    extensionHom K (s + 1) (upper (alternating p)) ∈ elementaryRootGroup K (s + 1) := by
  let H := (elementaryRootGroup K (s + 1)).comap (extensionHom K (s + 1))
  let P := upperParameters H
  change alternating p ∈ P
  rw [alternating_sum]
  apply P.sum_mem
  intro i _
  apply P.sum_mem
  intro j _
  by_cases hij : i.val < j.val
  · exact upper_pair_mem K h2 s i j (fun he => (Nat.ne_of_lt hij) (congrArg Fin.val he)) _
  · simp only [strictUpper, dif_neg hij, Matrix.single_zero, sub_zero]
    exact P.zero_mem

theorem lower_alternating_mem (h2 : (2 : K) ≠ 0) (s : ℕ) (p : Parameters K (s + 1)) :
    extensionHom K (s + 1) (lower (alternating p)) ∈ elementaryRootGroup K (s + 1) := by
  let H := (elementaryRootGroup K (s + 1)).comap (extensionHom K (s + 1))
  let P := lowerParameters H
  change alternating p ∈ P
  rw [alternating_sum]
  apply P.sum_mem
  intro i _
  apply P.sum_mem
  intro j _
  by_cases hij : i.val < j.val
  · exact lower_pair_mem K h2 s i j (fun he => (Nat.ne_of_lt hij) (congrArg Fin.val he)) _
  · simp only [strictUpper, dif_neg hij, Matrix.single_zero, sub_zero]
    exact P.zero_mem

end SymmetricSubgroupAsymptotics.CFSGOrthogonalBIndexShears
