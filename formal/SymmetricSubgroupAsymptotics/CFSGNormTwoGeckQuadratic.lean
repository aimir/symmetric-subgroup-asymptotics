import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckColumns

/-! The actual second divided-power coefficient of a norm-two Geck root.
It is the integral single-entry map v_-i -> v_i. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoGeckQuadratic
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing CFSGNormTwoRootStrings
open CFSGNormTwoPairingBounds CFSGNormTwoGeckColumns
variable {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℤ) (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    [Fintype (Roots A)] [DecidableEq (Roots A)]
    (b : (rootPairing A hs hp).Base)

def secondMatrix (i : b.support) : Matrix (b.support⊕Roots A) (b.support⊕Roots A) ℚ :=
  Matrix.single (Sum.inr (i:Roots A)) (Sum.inr (negativeIndex A hs hp i)) 1

theorem E_square_u (i j : b.support) :
    (RootPairing.GeckConstruction.e i)^2 *ᵥRootPairing.GeckConstruction.u j=0 := by
  rw [pow_two,←Matrix.mulVec_mulVec,E_u A hs hp b i j,Matrix.mulVec_smul,
    E_v_self A hs hp b i,smul_zero]

theorem E_square_v_other (i : b.support) (j : Roots A) (hj : j≠negativeIndex A hs hp i) :
    (RootPairing.GeckConstruction.e i)^2 *ᵥRootPairing.GeckConstruction.v b j=0 := by
  by_cases ha : (rootPairing A hs hp).root i+(rootPairing A hs hp).root j∈
      Set.range (rootPairing A hs hp).root
  · obtain ⟨k,hk⟩ := ha
    rw [pow_two,←Matrix.mulVec_mulVec,E_v_add A hs hp b i j k hk]
    have hv : k.val=(i:Roots A).val+j.val := by
      ext t
      have ht := congrFun hk t
      change (k.val t:ℚ)=((i:Roots A).val t:ℚ)+(j.val t:ℚ) at ht
      exact_mod_cast ht
    have hadd := pairing_of_root_add A hs hp hk
    have hcoeff : integerPairing A (i:Roots A).val k.val=1 := by
      rw [hv,map_add,(i:Roots A).property,hadd]
      norm_num
    apply E_v_zero A hs hp b i k
    · intro hki
      rw [hki,negative_val A hs hp,map_neg,(i:Roots A).property] at hcoeff
      norm_num at hcoeff
    · rintro ⟨l,hl⟩
      have hbad := pairing_of_root_add A hs hp hl
      omega
  · rw [pow_two,←Matrix.mulVec_mulVec,E_v_zero A hs hp b i j hj ha,
      Matrix.mulVec_zero]

theorem E_square_v_negative (i : b.support) :
    (RootPairing.GeckConstruction.e i)^2 *ᵥRootPairing.GeckConstruction.v b (negativeIndex A hs hp i)=
      (2:ℚ) • RootPairing.GeckConstruction.v b i := by
  rw [pow_two,←Matrix.mulVec_mulVec,E_v_negative A hs hp b i,E_u A hs hp b i i,
    RootPairing.Base.cartanMatrix_apply_same]
  norm_num <;> ext k <;> simp [Pi.mul_apply,Pi.smul_apply,smul_eq_mul]

theorem second_on_basis (i : b.support) (j : b.support⊕Roots A) :
    secondMatrix A hs hp b i *ᵥPi.single j 1=
      if j=Sum.inr (negativeIndex A hs hp i) then RootPairing.GeckConstruction.v b i else 0 := by
  rw [Matrix.mulVec_single_one]
  ext k
  by_cases hj : j=Sum.inr (negativeIndex A hs hp i)
  · subst j
    simp [secondMatrix,RootPairing.GeckConstruction.v,Matrix.single_apply,Pi.single_apply,eq_comm]
  · simp [secondMatrix,Matrix.single_apply,hj,Ne.symm hj]

theorem E_square (i : b.support) :
    (RootPairing.GeckConstruction.e i)^2=(2:ℚ) • secondMatrix A hs hp b i := by
  apply Matrix.ext_of_mulVec_single
  intro j
  rw [Matrix.smul_mulVec,second_on_basis]
  cases j with
  | inl j =>
      change (RootPairing.GeckConstruction.e i)^2 *ᵥRootPairing.GeckConstruction.u j=_
      rw [E_square_u A hs hp b i j]
      simp
  | inr j =>
      change (RootPairing.GeckConstruction.e i)^2 *ᵥRootPairing.GeckConstruction.v b j=_
      by_cases hj : j=negativeIndex A hs hp i
      · subst j
        rw [E_square_v_negative A hs hp b i]
        simp
      · rw [E_square_v_other A hs hp b i j hj]
        simp [hj]

end SymmetricSubgroupAsymptotics.CFSGNormTwoGeckQuadratic
