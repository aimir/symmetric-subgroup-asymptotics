import SymmetricSubgroupAsymptotics.CFSGTwistedDNaturalFork
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDElementaryGroup

/-! The literal paired positive fork word retains its quadratic cross
term. Its actual vector action, not an infinitesimal substitute, is used
for defining-characteristic singular-flag recovery. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGTwistedDForkPositiveAction
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDGenerationForkTorus CFSGTwistedDNaturalFork
variable (K : Type) [Field K]

private theorem single_mulVec {r : ℕ} (i j : Index r) (a : K) (v : Index r → K) :
    Matrix.single i j a *ᵥ v = Pi.single i (a * v j) := by
  funext x
  by_cases hx : x = i
  · subst x
    simp [Matrix.mulVec, dotProduct, Matrix.single_apply]
  · simp [Matrix.mulVec, dotProduct, hx, Ne.symm hx]

def foldedFork (s : ℕ) : (Mat K (s + 2))ˣ :=
  rootTransvection K (s + 2) false (pen s) 1 * rootTransvection K (s + 2) false (last s) 1

theorem foldedFork_val (s : ℕ) :
    (foldedFork K s : Mat K (s + 2)) =
      1 + (Matrix.single (Sum.inl (pen s)) (Sum.inl (last s)) 1 -
        Matrix.single (Sum.inr (last s)) (Sum.inr (pen s)) 1) +
      (Matrix.single (Sum.inl (pen s)) (Sum.inr (last s)) 1 -
        Matrix.single (Sum.inl (last s)) (Sum.inr (pen s)) 1) -
      Matrix.single (Sum.inl (pen s)) (Sum.inr (pen s)) 1 := by
  have hp : (pen s).val + 1 < s + 2 := by simp [pen]
  have hl : ¬(last s).val + 1 < s + 2 := by simp [last]
  have hs : (⟨(pen s).val + 1, hp⟩ : Fin (s + 2)) = last s := by
    apply Fin.ext
    simp [pen, last]
  simp only [foldedFork, Units.val_mul, rootTransvection_val, rootMatrix,
    Bool.false_eq_true, if_false, one_smul]
  rw [positive, dif_pos hp, hs, positive, dif_neg hl, previous_last]
  simp only [mul_add, add_mul, mul_sub, sub_mul, one_mul, mul_one]
  simp [Ne.symm (pen_ne_last s)]
  abel

theorem foldedFork_mulVec (s : ℕ) (v : Index (s + 2) → K) :
    (foldedFork K s : Mat K (s + 2)) *ᵥ v =
      v + (Pi.single (Sum.inl (pen s)) (v (Sum.inl (last s))) -
        Pi.single (Sum.inr (last s)) (v (Sum.inr (pen s)))) +
      (Pi.single (Sum.inl (pen s)) (v (Sum.inr (last s))) -
        Pi.single (Sum.inl (last s)) (v (Sum.inr (pen s)))) -
      Pi.single (Sum.inl (pen s)) (v (Sum.inr (pen s))) := by
  rw [foldedFork_val]
  simp only [Matrix.add_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec, single_mulVec, one_mul]

theorem chain_positive_action {r : ℕ} (i : Fin r) (hi : i.val + 1 < r)
    (v : Index r → K) :
    ((rootTransvection K r false i 1 : Mat K r) *ᵥ v) (Sum.inl i) =
      v (Sum.inl i) + v (Sum.inl (⟨i.val + 1, hi⟩ : Fin r)) := by
  simp only [rootTransvection_val, rootMatrix, Bool.false_eq_true, if_false, one_smul,
    positive, dif_pos hi, Matrix.add_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec,
    single_mulVec, one_mul]
  simp

theorem chain_negative_action {r : ℕ} (i : Fin r) (hi : i.val + 1 < r)
    (v : Index r → K) :
    ((rootTransvection K r false i 1 : Mat K r) *ᵥ v)
      (Sum.inr (⟨i.val + 1, hi⟩ : Fin r)) =
      v (Sum.inr (⟨i.val + 1, hi⟩ : Fin r)) - v (Sum.inr i) := by
  simp only [rootTransvection_val, rootMatrix, Bool.false_eq_true, if_false, one_smul,
    positive, dif_pos hi, Matrix.add_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec,
    single_mulVec, one_mul]
  simp [sub_eq_add_neg]

end SymmetricSubgroupAsymptotics.CFSGTwistedDForkPositiveAction
