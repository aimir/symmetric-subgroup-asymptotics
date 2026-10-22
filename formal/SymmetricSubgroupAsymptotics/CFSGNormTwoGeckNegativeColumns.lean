import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckColumns

/-! Literal negative-root columns for the same norm-two Geck matrices.
These complement the checked positive-root columns for Weyl-word calculations. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoGeckNegativeColumns
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing CFSGNormTwoRootStrings
open CFSGNormTwoGeckColumns
variable {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℤ) (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    [Fintype (Roots A)] [DecidableEq (Roots A)]
    (b : (rootPairing A hs hp).Base)

theorem F_v_self (i : b.support) :
    RootPairing.GeckConstruction.f i*ᵥRootPairing.GeckConstruction.v b i=
      RootPairing.GeckConstruction.u i :=
  RootPairing.GeckConstruction.f_lie_v_same i

theorem F_u (i j : b.support) :
    RootPairing.GeckConstruction.f i*ᵥRootPairing.GeckConstruction.u j=
      |b.cartanMatrix i j| • RootPairing.GeckConstruction.v b (negativeIndex A hs hp i) := by
  change RootPairing.GeckConstruction.f i*ᵥPi.single (Sum.inl j) 1=_
  rw [Matrix.mulVec_single_one]
  ext (k|k) <;>
    simp [RootPairing.GeckConstruction.f,RootPairing.GeckConstruction.v,
      negativeIndex,RootPairing.indexNeg_neg,Pi.single_apply]

theorem F_v_sub (i : b.support) (j k : Roots A)
    (hk : (rootPairing A hs hp).root k=
      (rootPairing A hs hp).root j-(rootPairing A hs hp).root i) :
    RootPairing.GeckConstruction.f i*ᵥRootPairing.GeckConstruction.v b j=
      RootPairing.GeckConstruction.v b k := by
  have hr : (rootPairing A hs hp).root j=
      (rootPairing A hs hp).root k+(rootPairing A hs hp).root i := by
    rw [hk]
    abel
  have he := RootPairing.GeckConstruction.f_lie_v_ne (b:=b) hr
  change RootPairing.GeckConstruction.f i*ᵥRootPairing.GeckConstruction.v b j=
    ((rootPairing A hs hp).chainTopCoeff i j+1:ℚ) • RootPairing.GeckConstruction.v b k at he
  rw [chainTopCoeff_of_root_sub A hs hp hk] at he
  simpa only [Nat.cast_zero,zero_add,one_smul] using he

theorem F_v_zero (i : b.support) (j : Roots A) (hj : j≠i)
    (ha : (rootPairing A hs hp).root j-(rootPairing A hs hp).root i∉
      Set.range (rootPairing A hs hp).root) :
    RootPairing.GeckConstruction.f i*ᵥRootPairing.GeckConstruction.v b j=0 := by
  have hn (k : Roots A) : (rootPairing A hs hp).root k≠
      (rootPairing A hs hp).root j-(rootPairing A hs hp).root i := fun h=>ha ⟨k,h⟩
  change RootPairing.GeckConstruction.f i*ᵥPi.single (Sum.inr j) 1=0
  rw [Matrix.mulVec_single_one]
  ext (k|k) <;> simp [RootPairing.GeckConstruction.f,hj,hn]

theorem F_v_negative (i : b.support) :
    RootPairing.GeckConstruction.f i*ᵥRootPairing.GeckConstruction.v b (negativeIndex A hs hp i)=0 := by
  apply F_v_zero A hs hp b i (negativeIndex A hs hp i)
  · exact Ne.symm (RootPairing.ne_neg (rootPairing A hs hp) i)
  · rintro ⟨k,hk⟩
    have he := pairing_of_root_sub A hs hp hk
    rw [negative_val,map_neg,i.val.property] at he
    norm_num at he

end SymmetricSubgroupAsymptotics.CFSGNormTwoGeckNegativeColumns
