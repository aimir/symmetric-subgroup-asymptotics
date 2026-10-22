import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckWeylSquareSign

/-! Adjacent simple-root operators anticommute with the square of the
actual Weyl operator. This is proved on the same norm-two root columns;
it is the matrix content needed for a genuine derived fixed-root word. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoGeckAdjacentWeylSign
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing CFSGNormTwoPairingBounds
open CFSGNormTwoGeckColumns CFSGNormTwoGeckWeylBasic CFSGNormTwoGeckWeylSquareSign
variable {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℤ) (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    [Fintype (Roots A)] [DecidableEq (Roots A)]
    (b : (rootPairing A hs hp).Base)

theorem weyl_square_e_anticommute (i j : b.support)
    (hij : integerPairing A (i:Roots A).val (j:Roots A).val= -1) :
    (weylOperator A hs hp b i)^2*eOperator A hs hp b j=
      -(eOperator A hs hp b j*(weylOperator A hs hp b i)^2) := by
  apply (Pi.basisFun ℚ (b.support⊕Roots A)).ext
  intro k
  cases k with
  | inl k=>
    have he : (Pi.basisFun ℚ (b.support⊕Roots A)) (.inl k)=RootPairing.GeckConstruction.u k := by
      rw [Pi.basisFun_apply]
    simp only [he,Module.End.mul_apply,LinearMap.neg_apply]
    have hej : eOperator A hs hp b j (RootPairing.GeckConstruction.u k)=
        (((|b.cartanMatrix j k|:ℤ):ℚ)) • RootPairing.GeckConstruction.v b j := by
      simpa only [Int.cast_smul_eq_zsmul] using E_u A hs hp b j k
    rw [hej,map_smul,weyl_square_root,weyl_square_cartan,hej,hij]
    norm_num [squareSign] <;> module
  | inr k=>
    have he : (Pi.basisFun ℚ (b.support⊕Roots A)) (.inr k)=RootPairing.GeckConstruction.v b k := by
      rw [Pi.basisFun_apply]
    simp only [he,Module.End.mul_apply,LinearMap.neg_apply]
    by_cases hneg : k=negativeIndex A hs hp j
    · subst k
      have hej : eOperator A hs hp b j
          (RootPairing.GeckConstruction.v b (negativeIndex A hs hp j))=
          RootPairing.GeckConstruction.u j := E_v_negative A hs hp b j
      have hc : integerPairing A (i:Roots A).val (negativeIndex A hs hp j).val=1 := by
        rw [negative_val,map_neg,hij]
        norm_num
      rw [hej,weyl_square_cartan,weyl_square_root,map_smul,hej,hc]
      norm_num [squareSign]
    · by_cases ha : (rootPairing A hs hp).root j+(rootPairing A hs hp).root k∈
          Set.range (rootPairing A hs hp).root
      · obtain ⟨l,hl⟩ := ha
        have hej : eOperator A hs hp b j (RootPairing.GeckConstruction.v b k)=
            RootPairing.GeckConstruction.v b l := E_v_add A hs hp b j k l hl
        have hv : l.val=(j:Roots A).val+k.val := by
          ext t
          have ht := congrFun hl t
          change (l.val t:ℚ)=((j:Roots A).val t:ℚ)+(k.val t:ℚ) at ht
          exact_mod_cast ht
        have hc : integerPairing A (i:Roots A).val l.val=
            integerPairing A (i:Roots A).val k.val-1 := by
          rw [hv,map_add,hij]
          ring
        have hk := root_pairing_bounds A hs hp (i:Roots A) k
        have hl' := root_pairing_bounds A hs hp (i:Roots A) l
        rw [hc] at hl'
        have hsign := squareSign_shift (integerPairing A (i:Roots A).val k.val) hk hl'
        rw [hej,weyl_square_root,weyl_square_root,map_smul,hej,hc,hsign,Int.cast_neg,neg_smul]
      · have hej : eOperator A hs hp b j (RootPairing.GeckConstruction.v b k)=0 :=
          E_v_zero A hs hp b j k hneg ha
        rw [hej,map_zero,weyl_square_root,map_smul,hej,smul_zero,neg_zero]

end SymmetricSubgroupAsymptotics.CFSGNormTwoGeckAdjacentWeylSign
