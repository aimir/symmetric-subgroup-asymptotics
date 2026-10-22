import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckFieldWeylColumns

/-! The actual Weyl word is a signed permutation on EVERY original
root column in every coefficient ring. The sign is an integer unit;
it is not discarded outside characteristic two. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoGeckSignedRootColumns
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing CFSGNormTwoPairingBounds
open CFSGNormTwoGeckColumns CFSGNormTwoGeckWeylBasic CFSGNormTwoRootNeighbors
open CFSGNormTwoGeckWeylRootStrings CFSGNormTwoGeckIntegralRealization
open CFSGNormTwoGeckFieldWeylColumns CFSGSerreQuadraticMatrix CFSGIntegerMatrixColumnTransport
variable {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℤ) (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    [Fintype (Roots A)] [DecidableEq (Roots A)] [(rootPairing A hs hp).IsIrreducible]
    (b : (rootPairing A hs hp).Base) {r : ℕ} (s : Fin r≃b.support)

theorem reflection_val (i k : Roots A) :
    ((rootPairing A hs hp).reflectionPerm i k).val=
      k.val-integerPairing A k.val i.val • i.val := rfl

theorem signed_root_column (K : Type*) [CommRing K] (i : Fin r) (k : Roots A) :
    ∃c : ℤ,(c=1 ∨ c= -1) ∧
      (canonicalWeyl (realizationData A hs hp b s) K i : Matrix
        (b.support⊕Roots A) (b.support⊕Roots A) K)*ᵥPi.single (.inr k) 1=
        (c:K) • Pi.single (.inr ((rootPairing A hs hp).reflectionPerm (s i) k)) 1 := by
  by_cases heq : k=s i
  · subst k
    refine ⟨1,Or.inl rfl,?_⟩
    simpa only [Int.cast_one,one_smul] using weyl_positive A hs hp b s K i
  by_cases hneg : k=negativeIndex A hs hp (s i)
  · subst k
    refine ⟨1,Or.inl rfl,?_⟩
    rw [negativeIndex,RootPairing.reflectionPerm_self]
    simpa only [Int.cast_one,one_smul] using weyl_negative A hs hp b s K i
  have hopp : (s i:Roots A).val≠ -k.val := by
    intro h
    apply hneg
    apply Subtype.ext
    rw [negative_val,h,neg_neg]
  rcases root_pairing_interior A hs hp (s i:Roots A) k (Ne.symm heq) hopp with h|h|h
  · obtain ⟨l,hl⟩ := (root_add_mem_iff A hs hp (s i) k).mpr h
    have hr : l=(rootPairing A hs hp).reflectionPerm (s i) k := by
      apply Subtype.ext
      apply castVector_injective
      change (rootPairing A hs hp).root l=
        (rootPairing A hs hp).root ((rootPairing A hs hp).reflectionPerm (s i) k)
      rw [RootPairing.root_reflectionPerm,RootPairing.reflection_apply_root,pairing_cast]
      rw [integer_symmetric A hs k.val (s i:Roots A).val,h]
      rw [hl]
      simp only [Int.cast_neg,Int.cast_one,neg_one_smul,sub_neg_eq_add]
      abel
    have hq := (weyl_pair_of_add A hs hp b (s i) k l hl).1
    have hc := field_column A hs hp b s K i (Pi.single (.inr k) 1) (Pi.single (.inr l) 1)
      (by simpa only [integerVector_single,Int.cast_one,RootPairing.GeckConstruction.v] using hq)
    refine ⟨1,Or.inl rfl,?_⟩
    simpa only [integerVector_single,Int.cast_one,hr,one_smul] using hc
  · have hr : (rootPairing A hs hp).reflectionPerm (s i) k=k := by
      apply Subtype.ext
      rw [reflection_val,integer_symmetric A hs k.val (s i:Roots A).val,h,zero_smul,sub_zero]
    have hq := weyl_fixed_of_pairing_zero A hs hp b (s i) k h
    have hc := field_column A hs hp b s K i (Pi.single (.inr k) 1) (Pi.single (.inr k) 1)
      (by simpa only [integerVector_single,Int.cast_one,RootPairing.GeckConstruction.v] using hq)
    refine ⟨1,Or.inl rfl,?_⟩
    simpa only [integerVector_single,Int.cast_one,hr,one_smul] using hc
  · obtain ⟨l,hl⟩ := (root_sub_mem_iff A hs hp (s i) k).mpr h
    have hkl : (rootPairing A hs hp).root k=
        (rootPairing A hs hp).root (s i)+(rootPairing A hs hp).root l := by rw [hl]; abel
    have hr : l=(rootPairing A hs hp).reflectionPerm (s i) k := by
      apply Subtype.ext
      apply castVector_injective
      change (rootPairing A hs hp).root l=
        (rootPairing A hs hp).root ((rootPairing A hs hp).reflectionPerm (s i) k)
      rw [RootPairing.root_reflectionPerm,RootPairing.reflection_apply_root,pairing_cast]
      rw [integer_symmetric A hs k.val (s i:Roots A).val,h,Int.cast_one,one_smul]
      exact hl
    have hq := (weyl_pair_of_add A hs hp b (s i) l k hkl).2
    have hc := field_column A hs hp b s K i (Pi.single (.inr k) 1) (-Pi.single (.inr l) 1)
      (by simpa only [integerVector_single,integerVector_neg,Int.cast_one,
        RootPairing.GeckConstruction.v] using hq)
    refine ⟨-1,Or.inr rfl,?_⟩
    simpa only [integerVector_single,integerVector_neg,Int.cast_neg,Int.cast_one,
      neg_one_smul,hr] using hc

end SymmetricSubgroupAsymptotics.CFSGNormTwoGeckSignedRootColumns
