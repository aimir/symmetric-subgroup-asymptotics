import SymmetricSubgroupAsymptotics.CFSGTwistedDNaturalFork

/-! Arbitrary-parameter action of the literal orthogonal terminal pair.
The product retains its quadratic cross term, also in characteristic two. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDForkPairAction
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDGenerationForkTorus CFSGTwistedDNaturalFork
variable (K : Type) [Field K]

private theorem single_mulVec {r : ℕ} (i j : Index r) (a : K) (v : Index r → K) :
    Matrix.single i j a *ᵥ v = Pi.single i (a * v j) := by
  funext x
  by_cases hx : x = i
  · subst x
    simp [Matrix.mulVec, dotProduct, Matrix.single_apply]
  · simp [Matrix.mulVec, dotProduct, hx, Ne.symm hx]

def forkPair (s : ℕ) (t u : K) : (Mat K (s + 2))ˣ :=
  rootTransvection K (s + 2) false (pen s) t * rootTransvection K (s + 2) false (last s) u

theorem forkPair_val (s : ℕ) (t u : K) :
    (forkPair K s t u : Mat K (s + 2)) =
      1 + (Matrix.single (Sum.inl (pen s)) (Sum.inl (last s)) t -
        Matrix.single (Sum.inr (last s)) (Sum.inr (pen s)) t) +
      (Matrix.single (Sum.inl (pen s)) (Sum.inr (last s)) u -
        Matrix.single (Sum.inl (last s)) (Sum.inr (pen s)) u) -
      Matrix.single (Sum.inl (pen s)) (Sum.inr (pen s)) (t * u) := by
  have hp : (pen s).val + 1 < s + 2 := by simp [pen]
  have hl : ¬(last s).val + 1 < s + 2 := by simp [last]
  have hs : (⟨(pen s).val + 1, hp⟩ : Fin (s + 2)) = last s := by
    apply Fin.ext
    simp [pen, last]
  simp only [forkPair, Units.val_mul, rootTransvection_val, rootMatrix,
    Bool.false_eq_true, if_false]
  rw [positive, dif_pos hp, hs, positive, dif_neg hl, previous_last]
  simp only [smul_sub, Matrix.smul_single, smul_eq_mul, mul_one,
    mul_add, add_mul, mul_sub, sub_mul, one_mul]
  simp [Ne.symm (pen_ne_last s)]
  abel

theorem forkPair_mulVec (s : ℕ) (t u : K) (v : Index (s + 2) → K) :
    (forkPair K s t u : Mat K (s + 2)) *ᵥ v =
      v + (Pi.single (Sum.inl (pen s)) (t * v (Sum.inl (last s))) -
        Pi.single (Sum.inr (last s)) (t * v (Sum.inr (pen s)))) +
      (Pi.single (Sum.inl (pen s)) (u * v (Sum.inr (last s))) -
        Pi.single (Sum.inl (last s)) (u * v (Sum.inr (pen s)))) -
      Pi.single (Sum.inl (pen s)) (t * u * v (Sum.inr (pen s))) := by
  rw [forkPair_val]
  simp only [Matrix.add_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec, single_mulVec]

theorem positive_last (s : ℕ) (t u : K) (v : Index (s + 2) → K) :
    ((forkPair K s t u : Mat K (s + 2)) *ᵥ v) (Sum.inl (last s)) =
      v (Sum.inl (last s)) - u * v (Sum.inr (pen s)) := by
  rw [forkPair_mulVec]
  simp [Ne.symm (pen_ne_last s), sub_eq_add_neg]

theorem negative_last (s : ℕ) (t u : K) (v : Index (s + 2) → K) :
    ((forkPair K s t u : Mat K (s + 2)) *ᵥ v) (Sum.inr (last s)) =
      v (Sum.inr (last s)) - t * v (Sum.inr (pen s)) := by
  rw [forkPair_mulVec]
  simp [sub_eq_add_neg]

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDForkPairAction
