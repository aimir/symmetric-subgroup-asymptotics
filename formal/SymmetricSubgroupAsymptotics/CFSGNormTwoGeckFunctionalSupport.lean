import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckHeightSupport

/-! Homogeneous support for ANY actual integer linear functional on the
root lattice. This extends the height support computation to the exact
coroot pairing needed for the literal diagonal-torus conjugation. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoGeckFunctionalSupport
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing CFSGNormTwoGeckColumns
open CFSGNormTwoGeckNormalizedEntries CFSGNormTwoRootStepCoordinates
open CFSGNormTwoGeckIntegralRealization CFSGNormTwoGeckIntegralQuadratic
open CFSGSerreQuadraticMatrix CFSGNormTwoGeckFieldRootColumns
open CFSGNormTwoGeckHeightSupport
variable {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℤ) (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    [Fintype (Roots A)] [DecidableEq (Roots A)]
    (b : (rootPairing A hs hp).Base)

theorem rational_E_degree (f : (n→ℤ)→ₗ[ℤ]ℤ) (i : b.support)
    (j k : b.support⊕Roots A)
    (hne : weight A hs hp b f j≠weight A hs hp b f k+f (i:Roots A).val) :
    RootPairing.GeckConstruction.e i j k=0 := by
  rcases j with j|j <;> rcases k with k|k
  · rfl
  · rw [E_inl_inr A hs hp b]
    split_ifs with h
    · rcases h with ⟨rfl,rfl⟩
      exfalso
      apply hne
      simp only [weight,negative_val,map_neg]
      abel
    · rfl
  · rw [E_inr_inl A hs hp b]
    split_ifs with h
    · subst j
      exfalso
      apply hne
      simp only [weight,zero_add]
    · rfl
  · rw [E_inr_inr A hs hp b]
    split_ifs with h
    · exfalso
      apply hne
      change f j.val=f k.val+f (i:Roots A).val
      rw [root_add_val A hs hp h,map_add]
      exact add_comm _ _
    · rfl

theorem integer_E_degree (f : (n→ℤ)→ₗ[ℤ]ℤ) (i : b.support)
    (j k : b.support⊕Roots A)
    (hne : weight A hs hp b f j≠weight A hs hp b f k+f (i:Roots A).val) :
    CFSGGeckIntegralMatrices.E b i j k=0 := by
  apply (Int.cast_injective : Function.Injective (Int.cast : ℤ→ℚ))
  have he := congrArg (fun M : Matrix (b.support⊕Roots A) (b.support⊕Roots A) ℚ=>M j k)
    (CFSGGeckIntegralMatrices.map_E b i)
  change (CFSGGeckIntegralMatrices.E b i j k:ℚ)=RootPairing.GeckConstruction.e i j k at he
  rw [he,rational_E_degree A hs hp b f i j k hne,Int.cast_zero]

variable [(rootPairing A hs hp).IsIrreducible] {r : ℕ} (s : Fin r≃b.support)

theorem field_E_degree (f : (n→ℤ)→ₗ[ℤ]ℤ) (K : Type*) [CommRing K]
    (i : Fin r) (j k : b.support⊕Roots A)
    (hne : weight A hs hp b f j≠weight A hs hp b f k+f (s i:Roots A).val) :
    fieldRoot (realizationData A hs hp b s) K false i j k=0 := by
  change (CFSGGeckIntegralMatrices.E b (s i) j k:K)=0
  rw [integer_E_degree A hs hp b f (s i) j k hne,Int.cast_zero]

theorem field_second_degree (f : (n→ℤ)→ₗ[ℤ]ℤ) (K : Type*) [CommRing K]
    (i : Fin r) (j k : b.support⊕Roots A)
    (hne : weight A hs hp b f j≠weight A hs hp b f k+2*f (s i:Roots A).val) :
    fieldSecond (realizationData A hs hp b s) K false i j k=0 := by
  rw [second_literal]
  by_cases hj : j=Sum.inr (s i:Roots A)
  · subst j
    by_cases hk : k=Sum.inr (negativeIndex A hs hp (s i))
    · subst k
      exfalso
      apply hne
      simp only [weight,negative_val,map_neg]
      ring
    · simp [Matrix.single_apply,hk,eq_comm]
  · simp [Matrix.single_apply,hj,eq_comm]

end SymmetricSubgroupAsymptotics.CFSGNormTwoGeckFunctionalSupport
