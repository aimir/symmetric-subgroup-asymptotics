import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateFunctionalRootLeading
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateRootStarInjection
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinatePositivePairCollecting
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinatePositivePairCommute
import SymmetricSubgroupAsymptotics.CFSGGradedMatrixCommutatorSecondLayer

/-! The genuine
positive-pair group law and the exact degree-two layer give the Lie
coefficient in characteristic two, avoiding separate rational Lie casts. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateFunctionalPairBracket
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing CFSGNormTwoGeckLatticeDegree
open CFSGNormTwoCoordinateFunctionalRootLeading CFSGNormTwoCoordinateRootStarInjection
open CFSGNormTwoCoordinateSelectedRootElement CFSGNormTwoCoordinateRootBracketTransport
open CFSGNormTwoCoordinatePositivePairCollecting CFSGNormTwoCoordinatePositivePairCommute
open CFSGGradedMatrixGroupFirstLayer CFSGGradedMatrixCommutatorSecondLayer
open CFSGGradedMatrixSingleDegreeSpan CFSGGradedMatrixSubgroups
variable {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ) (hd : ∀i,A i i=2)
    (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    (ho : ∀i j,i≠j→A i j≤0)
    [Fintype (Roots A)] [DecidableEq (Roots A)]
    [(rootPairing A hs hp).IsReduced] [(rootPairing A hs hp).IsIrreducible]
local notation "ell" => latticeWeight A hs hp (coordinateBase A hd hs hp ho)
variable (K : Type) [Field K] [CharP K 2] (f : (Fin r→ℤ)→+ℤ)
    (k l : Roots A) (hk : ∀i,0≤k.val i) (hl : ∀i,0≤l.val i)
    (hfk : f k.val=1) (hfl : f l.val=1)
include f hk hl hfk hfl

theorem adjacent_coefficient_bracket
    (hpair : integerPairing A k.val l.val= -1) :
    ⁅selectedFieldCoefficient A hd hs hp ho K k,
      selectedFieldCoefficient A hd hs hp ho K l⁆=
      selectedFieldCoefficient A hd hs hp ho K (sumRoot A hs k l hpair) := by
  obtain ⟨e,he,hword⟩ := positive_pair_commutator_sign A hd hs hp ho k l hk hl hpair
  have heK : (e : K)=1 := by
    rcases he with rfl|rfl
    · exact Int.cast_one
    · simp only [Int.cast_neg,Int.cast_one,CharTwo.neg_eq]
  have hw := hword K (1 : K) 1
  rw [heK,one_mul,one_mul] at hw
  have hd2 : f (sumRoot A hs k l hpair).val=2 := by
    change f (k.val+l.val)=2
    rw [map_add,hfk,hfl]
    rfl
  have hlead := (selected_functional_cut_and_leading A hd hs hp ho K f
    (sumRoot A hs k l hpair) (by rw [hd2]; decide) 1).2
  rw [hd2,one_smul] at hlead
  have hfirstk : firstLayer (f∘ell) (selectedRootElement A hd hs hp ho K k 1)=
      selectedFieldCoefficient A hd hs hp ho K k := by
    simpa only [functionalWeight,one_smul] using
      root_firstLayer A hd hs hp ho K f k hfk (1 : K)
  have hfirstl : firstLayer (f∘ell) (selectedRootElement A hd hs hp ho K l 1)=
      selectedFieldCoefficient A hd hs hp ho K l := by
    simpa only [functionalWeight,one_smul] using
      root_firstLayer A hd hs hp ho K f l hfl (1 : K)
  have hbr := commutator_secondLayer (f∘ell)
    (selectedRootElement A hd hs hp ho K k 1)
    (selectedRootElement A hd hs hp ho K l 1)
    (root_strict A hd hs hp ho K f k hfk 1)
    (root_strict A hd hs hp ho K f l hfl 1)
  rw [hfirstk,hfirstl] at hbr
  exact hbr.symm.trans ((congrArg
    (fun u : (Matrix ((coordinateBase A hd hs hp ho).support⊕Roots A)
        ((coordinateBase A hd hs hp ho).support⊕Roots A) K)ˣ =>
      degreePart (f∘ell) (2:ℤ) (u.val-1)) hw).trans hlead)

omit [CharP K 2] in
theorem nonadjacent_coefficient_bracket
    (hpair : integerPairing A k.val l.val=0 ∨ integerPairing A k.val l.val=1) :
    ⁅selectedFieldCoefficient A hd hs hp ho K k,
      selectedFieldCoefficient A hd hs hp ho K l⁆=0 := by
  have hc := positive_pair_commute A hd hs hp ho K k l hk hl hpair 1 1
  have hw : selectedRootElement A hd hs hp ho K k 1*
      selectedRootElement A hd hs hp ho K l 1*
      (selectedRootElement A hd hs hp ho K k 1)⁻¹*
      (selectedRootElement A hd hs hp ho K l 1)⁻¹=1 := by
    rw [hc.eq]
    group
  have hfirstk : firstLayer (f∘ell) (selectedRootElement A hd hs hp ho K k 1)=
      selectedFieldCoefficient A hd hs hp ho K k := by
    simpa only [functionalWeight,one_smul] using
      root_firstLayer A hd hs hp ho K f k hfk (1 : K)
  have hfirstl : firstLayer (f∘ell) (selectedRootElement A hd hs hp ho K l 1)=
      selectedFieldCoefficient A hd hs hp ho K l := by
    simpa only [functionalWeight,one_smul] using
      root_firstLayer A hd hs hp ho K f l hfl (1 : K)
  have hbr := commutator_secondLayer (f∘ell)
    (selectedRootElement A hd hs hp ho K k 1)
    (selectedRootElement A hd hs hp ho K l 1)
    (root_strict A hd hs hp ho K f k hfk 1)
    (root_strict A hd hs hp ho K f l hfl 1)
  rw [hfirstk,hfirstl,hw] at hbr
  simpa only [Units.val_one,sub_self,map_zero] using hbr.symm

end SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateFunctionalPairBracket
