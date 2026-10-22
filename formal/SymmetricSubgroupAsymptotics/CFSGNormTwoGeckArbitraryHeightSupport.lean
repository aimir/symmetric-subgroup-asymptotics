import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckHeightSupport
import SymmetricSubgroupAsymptotics.CFSGGradedMatrixSupport

/-! The original Geck operators are homogeneous for EVERY integral
lattice functional. In particular, a simple root of height zero preserves
the blocks, whereas a root of positive height is strictly unipotent for
that grading. These statements hold in all characteristics. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoGeckArbitraryHeightSupport
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing CFSGNormTwoRootStepCoordinates
open CFSGNormTwoGeckNormalizedEntries CFSGNormTwoGeckColumns
open CFSGNormTwoGeckIntegralRealization CFSGNormTwoGeckHeightSupport
open CFSGSerreQuadraticMatrix CFSGNormTwoGeckFieldRootColumns
open CFSGGradedMatrixSupport
variable {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℤ) (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    [Fintype (Roots A)] [DecidableEq (Roots A)]
    (b : (rootPairing A hs hp).Base)

theorem rational_E_support (height : (n→ℤ)→ₗ[ℤ]ℤ) (i : b.support)
    (j k : b.support⊕Roots A)
    (hne : weight A hs hp b height j≠weight A hs hp b height k+height (i:Roots A).val) :
    RootPairing.GeckConstruction.e i j k=0 := by
  rcases j with j|j <;> rcases k with k|k
  · rfl
  · rw [E_inl_inr A hs hp b]
    split_ifs with h
    · rcases h with ⟨rfl,rfl⟩
      exfalso
      apply hne
      simp only [weight,negative_val,map_neg,neg_add_cancel]
    · rfl
  · rw [E_inr_inl A hs hp b]
    split_ifs with h
    · subst j
      exact False.elim (hne (by simp only [weight,zero_add]))
    · rfl
  · rw [E_inr_inr A hs hp b]
    split_ifs with h
    · exfalso
      apply hne
      change height j.val=height k.val+height (i:Roots A).val
      rw [root_add_val A hs hp h,map_add]
      exact add_comm _ _
    · rfl

theorem integer_E_support (height : (n→ℤ)→ₗ[ℤ]ℤ) (i : b.support)
    (j k : b.support⊕Roots A)
    (hne : weight A hs hp b height j≠weight A hs hp b height k+height (i:Roots A).val) :
    CFSGGeckIntegralMatrices.E b i j k=0 := by
  apply (Int.cast_injective : Function.Injective (Int.cast : ℤ→ℚ))
  have he := congrArg (fun M : Matrix (b.support⊕Roots A) (b.support⊕Roots A) ℚ=>M j k)
    (CFSGGeckIntegralMatrices.map_E b i)
  change (CFSGGeckIntegralMatrices.E b i j k:ℚ)=RootPairing.GeckConstruction.e i j k at he
  rw [he,rational_E_support A hs hp b height i j k hne,Int.cast_zero]

variable [(rootPairing A hs hp).IsIrreducible] {r : ℕ} (s : Fin r≃b.support)

theorem field_E_support (height : (n→ℤ)→ₗ[ℤ]ℤ)
    (K : Type*) [CommRing K] (i : Fin r) :
    Supported (weight A hs hp b height) (fun w=>w+height (s i:Roots A).val)
      (fieldRoot (realizationData A hs hp b s) K false i) := by
  intro j k hjk
  change (CFSGGeckIntegralMatrices.E b (s i) j k:K)=0
  rw [integer_E_support A hs hp b height (s i) j k hjk,Int.cast_zero]

theorem field_second_support (height : (n→ℤ)→ₗ[ℤ]ℤ)
    (K : Type*) [CommRing K] (i : Fin r) :
    Supported (weight A hs hp b height) (fun w=>w+2*height (s i:Roots A).val)
      (fieldSecond (realizationData A hs hp b s) K false i) := by
  intro j k hjk
  rw [second_literal]
  by_cases hj : j=Sum.inr (s i:Roots A)
  · subst j
    by_cases hk : k=Sum.inr (negativeIndex A hs hp (s i))
    · subst k
      exfalso
      apply hjk
      simp only [weight,negative_val,map_neg]
      omega
    · simp [hk,eq_comm]
  · simp [hj,eq_comm]

theorem canonicalRoot_preserves (height : (n→ℤ)→ₗ[ℤ]ℤ)
    (K : Type*) [CommRing K] (i : Fin r) (t : K)
    (hi : height (s i:Roots A).val=0) :
    Supported (weight A hs hp b height) id
      (canonicalRoot (realizationData A hs hp b s) K false i t :
        Matrix (b.support⊕Roots A) (b.support⊕Roots A) K) := by
  intro j k hjk
  have hE := field_E_support A hs hp b s height K i j k
  have hD := field_second_support A hs hp b s height K i j k
  have hEj : fieldRoot (realizationData A hs hp b s) K false i j k=0 :=
    hE (by simpa only [hi,add_zero] using hjk)
  have hDj : fieldSecond (realizationData A hs hp b s) K false i j k=0 :=
    hD (by simpa only [hi,mul_zero,add_zero] using hjk)
  have hne : j≠k := by intro h;subst k;exact hjk rfl
  simp only [canonicalRoot_val,Matrix.add_apply,Matrix.smul_apply,hEj,hDj,
    smul_zero,add_zero,Matrix.one_apply,if_neg hne]

theorem canonicalRoot_strict (height : (n→ℤ)→ₗ[ℤ]ℤ)
    (K : Type*) [CommRing K] (i : Fin r) (t : K)
    (hi : 0<height (s i:Roots A).val)
    (j k : b.support⊕Roots A) (hjk : weight A hs hp b height j≤weight A hs hp b height k) :
    (canonicalRoot (realizationData A hs hp b s) K false i t :
        Matrix (b.support⊕Roots A) (b.support⊕Roots A) K) j k=
      (1 : Matrix (b.support⊕Roots A) (b.support⊕Roots A) K) j k := by
  have hE := field_E_support A hs hp b s height K i j k (by
    change weight A hs hp b height j≠weight A hs hp b height k+height (s i:Roots A).val
    omega)
  have hD := field_second_support A hs hp b s height K i j k (by
    change weight A hs hp b height j≠weight A hs hp b height k+2*height (s i:Roots A).val
    omega)
  simp only [canonicalRoot_val,Matrix.add_apply,Matrix.smul_apply,hE,hD,smul_zero,add_zero]

end SymmetricSubgroupAsymptotics.CFSGNormTwoGeckArbitraryHeightSupport
