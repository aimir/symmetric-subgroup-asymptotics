import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckWeylBasic
import SymmetricSubgroupAsymptotics.CFSGNormTwoRootNeighbors

/-! The remaining actual root columns of a norm-two Geck Weyl word.
All strings are constructed in the original integer lattice. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoGeckWeylRootStrings
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing CFSGNormTwoPairingBounds
open CFSGNormTwoGeckColumns CFSGNormTwoGeckNegativeColumns
open CFSGNormTwoRootStrings CFSGNormTwoRootNeighbors CFSGNormTwoGeckWeylBasic
open CFSGQuadraticWeylStrings
variable {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℤ) (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    [Fintype (Roots A)] [DecidableEq (Roots A)]
    (b : (rootPairing A hs hp).Base)

theorem E_zero_of_pairing (i : b.support) (j : Roots A)
    (h1 : integerPairing A (i:Roots A).val j.val≠ -1)
    (h2 : integerPairing A (i:Roots A).val j.val≠ -2) :
    eOperator A hs hp b i (RootPairing.GeckConstruction.v b j)=0 := by
  apply E_v_zero A hs hp b i j
  · intro hj
    apply h2
    rw [hj,negative_val,map_neg,(i:Roots A).property]
  · intro h
    exact h1 ((root_add_mem_iff A hs hp i j).mp h)

theorem F_zero_of_pairing (i : b.support) (j : Roots A)
    (h1 : integerPairing A (i:Roots A).val j.val≠1)
    (h2 : integerPairing A (i:Roots A).val j.val≠2) :
    fOperator A hs hp b i (RootPairing.GeckConstruction.v b j)=0 := by
  apply F_v_zero A hs hp b i j
  · intro hj
    apply h2
    rw [hj]
    exact (i:Roots A).property
  · intro h
    exact h1 ((root_sub_mem_iff A hs hp i j).mp h)

theorem weyl_fixed_of_pairing_zero (i : b.support) (j : Roots A)
    (h : integerPairing A (i:Roots A).val j.val=0) :
    weylOperator A hs hp b i (RootPairing.GeckConstruction.v b j)=
      RootPairing.GeckConstruction.v b j := by
  apply word_fixed (eOperator A hs hp b i) (fOperator A hs hp b i)
  · exact E_zero_of_pairing A hs hp b i j (by omega) (by omega)
  · exact F_zero_of_pairing A hs hp b i j (by omega) (by omega)

theorem weyl_pair_of_add (i : b.support) (j k : Roots A)
    (hk : (rootPairing A hs hp).root k=
      (rootPairing A hs hp).root i+(rootPairing A hs hp).root j) :
    weylOperator A hs hp b i (RootPairing.GeckConstruction.v b j)=
      RootPairing.GeckConstruction.v b k ∧
    weylOperator A hs hp b i (RootPairing.GeckConstruction.v b k)=
      -RootPairing.GeckConstruction.v b j := by
  have hj := pairing_of_root_add A hs hp hk
  have hv : k.val=(i:Roots A).val+j.val := by
    ext t
    have ht := congrFun hk t
    change (k.val t:ℚ)=((i:Roots A).val t:ℚ)+(j.val t:ℚ) at ht
    exact_mod_cast ht
  have hkpair : integerPairing A (i:Roots A).val k.val=1 := by
    rw [hv,map_add,(i:Roots A).property,hj]
    norm_num
  apply word_pair (eOperator A hs hp b i) (fOperator A hs hp b i)
  · exact E_v_add A hs hp b i j k hk
  · exact E_zero_of_pairing A hs hp b i k (by omega) (by omega)
  · exact F_zero_of_pairing A hs hp b i j (by omega) (by omega)
  · apply F_v_sub A hs hp b i k j
    rw [hk]
    abel

theorem weyl_four_root (i : b.support) (j : Roots A) :
    ((weylOperator A hs hp b i)^4) (RootPairing.GeckConstruction.v b j)=
      RootPairing.GeckConstruction.v b j := by
  by_cases heq : j=i
  · subst j
    exact weyl_four_positive A hs hp b i
  by_cases hneg : j=negativeIndex A hs hp i
  · subst j
    exact weyl_four_negative A hs hp b i
  have hopp : (i:Roots A).val≠ -j.val := by
    intro h
    apply hneg
    apply Subtype.ext
    rw [negative_val,h,neg_neg]
  rcases root_pairing_interior A hs hp (i:Roots A) j (Ne.symm heq) hopp with h|h|h
  · obtain ⟨k,hk⟩ := (root_add_mem_iff A hs hp i j).mpr h
    have hw := weyl_pair_of_add A hs hp b i j k hk
    simp only [pow_succ,pow_zero,Module.End.mul_apply,Module.End.one_apply,
      hw.1,hw.2,map_neg,neg_neg]
  · have hw := weyl_fixed_of_pairing_zero A hs hp b i j h
    simp only [pow_succ,pow_zero,Module.End.mul_apply,Module.End.one_apply,hw]
  · obtain ⟨k,hk⟩ := (root_sub_mem_iff A hs hp i j).mpr h
    have hkj : (rootPairing A hs hp).root j=
        (rootPairing A hs hp).root i+(rootPairing A hs hp).root k := by
      rw [hk]
      abel
    have hw := weyl_pair_of_add A hs hp b i k j hkj
    simp only [pow_succ,pow_zero,Module.End.mul_apply,Module.End.one_apply,
      hw.1,hw.2,map_neg,neg_neg]

theorem weyl_four (i : b.support) : (weylOperator A hs hp b i)^4=1 := by
  apply (Pi.basisFun ℚ (b.support⊕Roots A)).ext
  intro k
  cases k with
  | inl j=>
    have he : (Pi.basisFun ℚ (b.support⊕Roots A)) (.inl j)=RootPairing.GeckConstruction.u j := by
      rw [Pi.basisFun_apply]
    simp only [he,Module.End.one_apply]
    exact weyl_four_cartan A hs hp b i j
  | inr j=>
    have he : (Pi.basisFun ℚ (b.support⊕Roots A)) (.inr j)=RootPairing.GeckConstruction.v b j := by
      rw [Pi.basisFun_apply]
    simp only [he,Module.End.one_apply]
    exact weyl_four_root A hs hp b i j

end SymmetricSubgroupAsymptotics.CFSGNormTwoGeckWeylRootStrings
