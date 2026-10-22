import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckNormalizedEntries
import SymmetricSubgroupAsymptotics.CFSGNormTwoRootStepCoordinates
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckFieldRootColumns

/-! The actual positive Geck root and integral half raise the same
integer lattice grading by one and two, respectively. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoGeckHeightSupport
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing CFSGNormTwoGeckColumns
open CFSGNormTwoGeckNormalizedEntries CFSGNormTwoRootStepCoordinates
open CFSGNormTwoGeckIntegralRealization CFSGNormTwoGeckIntegralQuadratic
open CFSGSerreQuadraticMatrix CFSGNormTwoGeckFieldRootColumns
variable {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℤ) (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    [Fintype (Roots A)] [DecidableEq (Roots A)]
    (b : (rootPairing A hs hp).Base)

def weight (height : (n→ℤ)→ₗ[ℤ]ℤ) : b.support⊕Roots A→ℤ
  | .inl _=>0
  | .inr k=>height k.val

theorem rational_E_support (height : (n→ℤ)→ₗ[ℤ]ℤ)
    (hheight : ∀i : b.support,height (i:Roots A).val=1)
    (i : b.support) (j k : b.support⊕Roots A)
    (hne : weight A hs hp b height j≠weight A hs hp b height k+1) :
    RootPairing.GeckConstruction.e i j k=0 := by
  rcases j with j|j <;> rcases k with k|k
  · rfl
  · rw [E_inl_inr A hs hp b]
    split_ifs with h
    · rcases h with ⟨rfl,rfl⟩
      exfalso
      apply hne
      norm_num only [weight,negative_val,map_neg,hheight]
    · rfl
  · rw [E_inr_inl A hs hp b]
    split_ifs with h
    · subst j
      exfalso
      apply hne
      simp only [weight,hheight,zero_add]
    · rfl
  · rw [E_inr_inr A hs hp b]
    split_ifs with h
    · exfalso
      apply hne
      change height j.val=height k.val+1
      rw [root_add_val A hs hp h,map_add,hheight]
      omega
    · rfl

theorem integer_E_support (height : (n→ℤ)→ₗ[ℤ]ℤ)
    (hheight : ∀i : b.support,height (i:Roots A).val=1)
    (i : b.support) (j k : b.support⊕Roots A)
    (hne : weight A hs hp b height j≠weight A hs hp b height k+1) :
    CFSGGeckIntegralMatrices.E b i j k=0 := by
  apply (Int.cast_injective : Function.Injective (Int.cast : ℤ→ℚ))
  have he := congrArg (fun M : Matrix (b.support⊕Roots A) (b.support⊕Roots A) ℚ=>M j k)
    (CFSGGeckIntegralMatrices.map_E b i)
  change (CFSGGeckIntegralMatrices.E b i j k:ℚ)=RootPairing.GeckConstruction.e i j k at he
  rw [he,rational_E_support A hs hp b height hheight i j k hne,Int.cast_zero]

variable [(rootPairing A hs hp).IsIrreducible] {r : ℕ} (s : Fin r≃b.support)

theorem field_E_strict (height : (n→ℤ)→ₗ[ℤ]ℤ)
    (hheight : ∀i : b.support,height (i:Roots A).val=1)
    (K : Type*) [CommRing K] (i : Fin r) (j k : b.support⊕Roots A)
    (hjk : weight A hs hp b height j≤weight A hs hp b height k) :
    fieldRoot (realizationData A hs hp b s) K false i j k=0 := by
  change (CFSGGeckIntegralMatrices.E b (s i) j k:K)=0
  rw [integer_E_support A hs hp b height hheight (s i) j k (by omega),Int.cast_zero]

theorem field_second_strict (height : (n→ℤ)→ₗ[ℤ]ℤ)
    (hheight : ∀i : b.support,height (i:Roots A).val=1)
    (K : Type*) [CommRing K] (i : Fin r) (j k : b.support⊕Roots A)
    (hjk : weight A hs hp b height j≤weight A hs hp b height k) :
    fieldSecond (realizationData A hs hp b s) K false i j k=0 := by
  rw [second_literal]
  by_cases hj : j=Sum.inr (s i:Roots A)
  · subst j
    by_cases hk : k=Sum.inr (negativeIndex A hs hp (s i))
    · subst k
      have he : (1:ℤ)≤ -1 := by
        simpa only [weight,negative_val,map_neg,hheight] using hjk
      omega
    · simp [Matrix.single_apply,hk,eq_comm]
  · simp [Matrix.single_apply,hj,eq_comm]

end SymmetricSubgroupAsymptotics.CFSGNormTwoGeckHeightSupport
