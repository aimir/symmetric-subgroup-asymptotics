import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckAdjacentWeylSign

/-! The adjacent negative root has the same genuine Weyl-square parity
sign as its positive root. All calculations use the actual negative
norm-two Geck columns. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoGeckAdjacentWeylSign
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing CFSGNormTwoPairingBounds
open CFSGNormTwoGeckColumns CFSGNormTwoGeckNegativeColumns
open CFSGNormTwoGeckWeylBasic CFSGNormTwoGeckWeylSquareSign
variable {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℤ) (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    [Fintype (Roots A)] [DecidableEq (Roots A)]
    (b : (rootPairing A hs hp).Base)

theorem weyl_square_f_anticommute (i j : b.support)
    (hij : integerPairing A (i:Roots A).val (j:Roots A).val= -1) :
    (weylOperator A hs hp b i)^2*fOperator A hs hp b j=
      -(fOperator A hs hp b j*(weylOperator A hs hp b i)^2) := by
  apply (Pi.basisFun ℚ (b.support⊕Roots A)).ext
  intro k
  cases k with
  | inl k=>
    have he : (Pi.basisFun ℚ (b.support⊕Roots A)) (.inl k)=RootPairing.GeckConstruction.u k := by
      rw [Pi.basisFun_apply]
    simp only [he,Module.End.mul_apply,LinearMap.neg_apply]
    have hfj : fOperator A hs hp b j (RootPairing.GeckConstruction.u k)=
        (((|b.cartanMatrix j k|:ℤ):ℚ)) •
          RootPairing.GeckConstruction.v b (negativeIndex A hs hp j) := by
      simpa only [Int.cast_smul_eq_zsmul] using F_u A hs hp b j k
    have hc : integerPairing A (i:Roots A).val (negativeIndex A hs hp j).val=1 := by
      rw [negative_val,map_neg,hij]
      norm_num
    rw [hfj,map_smul,weyl_square_root,weyl_square_cartan,hfj,hc]
    norm_num [squareSign] <;> module
  | inr k=>
    have he : (Pi.basisFun ℚ (b.support⊕Roots A)) (.inr k)=RootPairing.GeckConstruction.v b k := by
      rw [Pi.basisFun_apply]
    simp only [he,Module.End.mul_apply,LinearMap.neg_apply]
    by_cases hself : k=j
    · subst k
      have hfj : fOperator A hs hp b j (RootPairing.GeckConstruction.v b j)=
          RootPairing.GeckConstruction.u j := F_v_self A hs hp b j
      rw [hfj,weyl_square_cartan,weyl_square_root,map_smul,hfj,hij]
      norm_num [squareSign]
    · by_cases ha : (rootPairing A hs hp).root k-(rootPairing A hs hp).root j∈
          Set.range (rootPairing A hs hp).root
      · obtain ⟨l,hl⟩ := ha
        have hfj : fOperator A hs hp b j (RootPairing.GeckConstruction.v b k)=
            RootPairing.GeckConstruction.v b l := F_v_sub A hs hp b j k l hl
        have hv : l.val=k.val-(j:Roots A).val := by
          ext t
          have ht := congrFun hl t
          change (l.val t:ℚ)=(k.val t:ℚ)-((j:Roots A).val t:ℚ) at ht
          exact_mod_cast ht
        have hc : integerPairing A (i:Roots A).val l.val=
            integerPairing A (i:Roots A).val k.val+1 := by
          rw [hv,map_sub,hij]
          ring
        have hk := root_pairing_bounds A hs hp (i:Roots A) k
        have hl' := root_pairing_bounds A hs hp (i:Roots A) l
        rw [hc] at hl'
        have hsign : squareSign (integerPairing A (i:Roots A).val k.val+1)=
            -squareSign (integerPairing A (i:Roots A).val k.val) := by
          have hh := squareSign_shift (integerPairing A (i:Roots A).val k.val+1) hl'
            (by simpa only [add_sub_cancel_right] using hk)
          simp only [add_sub_cancel_right] at hh
          omega
        rw [hfj,weyl_square_root,weyl_square_root,map_smul,hfj,hc,hsign,Int.cast_neg,neg_smul]
      · have hfj : fOperator A hs hp b j (RootPairing.GeckConstruction.v b k)=0 :=
          F_v_zero A hs hp b j k hself ha
        rw [hfj,map_zero,weyl_square_root,map_smul,hfj,smul_zero,neg_zero]

end SymmetricSubgroupAsymptotics.CFSGNormTwoGeckAdjacentWeylSign
