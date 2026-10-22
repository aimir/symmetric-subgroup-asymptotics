import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckWeylRootStrings

/-! The square of the actual norm-two Weyl word is the integral weight
parity sign. This is derived from the proved one/two/three root strings,
not from a named finite-group torus relation. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoGeckWeylSquareSign
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing CFSGNormTwoPairingBounds
open CFSGNormTwoGeckColumns CFSGNormTwoRootNeighbors
open CFSGNormTwoGeckWeylBasic CFSGNormTwoGeckWeylRootStrings
variable {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℤ) (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    [Fintype (Roots A)] [DecidableEq (Roots A)]
    (b : (rootPairing A hs hp).Base)

def squareSign (c : ℤ) : ℤ := if c= -1 ∨ c=1 then -1 else 1

theorem weyl_square_cartan (i j : b.support) :
    ((weylOperator A hs hp b i)^2) (RootPairing.GeckConstruction.u j)=
      RootPairing.GeckConstruction.u j := by
  have hi := (weyl_on_triple A hs hp b i).1
  have hj := weyl_on_cartan A hs hp b i j
  simp only [pow_two,Module.End.mul_apply,hj,map_sub,map_smul,hi]
  module

theorem weyl_square_root (i : b.support) (j : Roots A) :
    ((weylOperator A hs hp b i)^2) (RootPairing.GeckConstruction.v b j)=
      (squareSign (integerPairing A (i:Roots A).val j.val):ℚ) •
        RootPairing.GeckConstruction.v b j := by
  by_cases heq : j=i
  · subst j
    have hw := weyl_on_triple A hs hp b i
    simp only [pow_two,Module.End.mul_apply,hw.2.1,hw.2.2,(i:Roots A).property]
    norm_num [squareSign]
  by_cases hneg : j=negativeIndex A hs hp i
  · subst j
    have hw := weyl_on_triple A hs hp b i
    have hc : integerPairing A (i:Roots A).val (negativeIndex A hs hp i).val= -2 := by
      rw [negative_val,map_neg,(i:Roots A).property]
    simp only [pow_two,Module.End.mul_apply,hw.2.1,hw.2.2,hc]
    norm_num [squareSign]
  have hopp : (i:Roots A).val≠ -j.val := by
    intro h
    apply hneg
    apply Subtype.ext
    rw [negative_val,h,neg_neg]
  rcases root_pairing_interior A hs hp (i:Roots A) j (Ne.symm heq) hopp with h|h|h
  · obtain ⟨k,hk⟩ := (root_add_mem_iff A hs hp i j).mpr h
    have hw := weyl_pair_of_add A hs hp b i j k hk
    simp only [pow_two,Module.End.mul_apply,hw.1,hw.2,h]
    norm_num [squareSign]
  · have hw := weyl_fixed_of_pairing_zero A hs hp b i j h
    simp only [pow_two,Module.End.mul_apply,hw,h]
    norm_num [squareSign]
  · obtain ⟨k,hk⟩ := (root_sub_mem_iff A hs hp i j).mpr h
    have hkj : (rootPairing A hs hp).root j=
        (rootPairing A hs hp).root i+(rootPairing A hs hp).root k := by
      rw [hk]
      abel
    have hw := weyl_pair_of_add A hs hp b i k j hkj
    simp only [pow_two,Module.End.mul_apply,hw.2,map_neg,hw.1,h]
    norm_num [squareSign]

theorem squareSign_shift (c : ℤ) (hc : -2 ≤ c ∧ c ≤ 2) (hd : -2 ≤ c-1 ∧ c-1 ≤ 2) :
    squareSign (c-1)= -squareSign c := by
  have hlow : -1 ≤ c := by omega
  have hhigh : c ≤ 2 := hc.2
  interval_cases c <;> decide

end SymmetricSubgroupAsymptotics.CFSGNormTwoGeckWeylSquareSign
