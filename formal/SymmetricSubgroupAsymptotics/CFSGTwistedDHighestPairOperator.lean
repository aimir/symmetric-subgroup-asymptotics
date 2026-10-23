import SymmetricSubgroupAsymptotics.CFSGTwistedDFixedQuadraticAction
import SymmetricSubgroupAsymptotics.CFSGTwistedDRelativeHighestRoot
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexPairOperator

/-! The actual relative highest-root displacement on the fixed-field
quadratic space is its alternating pair operator. All parameters and
both natural vectors lie in the SAME fixed carrier, including at q=2. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGTwistedDHighestPairOperator
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDIndexFlagVectors
open CFSGTwistedDRelativeHighestRoot CFSGTwistedDFixedQuadraticAction
open CFSGTwistedDFixedQuadraticSpace CFSGTwistedA2FixedField CFSGAlternatingPairOperator
open CFSGTwistedDRelativeElementaryGroup CFSGOrthogonalDGenerationForkTorus

def positiveBasis (n : ℕ) (q : CFSG.PrimePower) (i : Fin (n + 2)) (hi : i ≠ last n) :
    fixedSpace n q :=
  ⟨Pi.single (Sum.inl i) 1,
    CFSGTwistedDNormalizeFirstPair.fixed_basis (q.Extension 2) n
      (CFSGSerreOrdinaryTwists.definingFieldAutomorphism q 2) (Sum.inl i)
      (by rw [CFSGTwistedDNaturalFork.flip_pos, if_neg hi])⟩

private theorem zero_ne_last (s : ℕ) : (0 : Fin (s + 4)) ≠ last (s + 2) := by
  intro h
  have hv := congrArg Fin.val h
  change 0 = s + 3 at hv
  omega

private theorem second_ne_last (s : ℕ) : secondIndex s ≠ last (s + 2) := by
  intro h
  have hv := congrArg Fin.val h
  change 1 = s + 3 at hv
  omega

def firstVector (s : ℕ) (q : CFSG.PrimePower) : fixedSpace (s + 2) q :=
  positiveBasis (s + 2) q 0 (zero_ne_last s)

def secondVector (s : ℕ) (q : CFSG.PrimePower) : fixedSpace (s + 2) q :=
  positiveBasis (s + 2) q (secondIndex s) (second_ne_last s)

theorem firstVector_val (s : ℕ) (q : CFSG.PrimePower) :
    (firstVector s q).val = CFSGOrthogonalDIndexFlagVectors.firstVector (q.Extension 2) s := rfl

theorem secondVector_val (s : ℕ) (q : CFSG.PrimePower) :
    (secondVector s q).val = CFSGOrthogonalDIndexFlagVectors.secondVector (q.Extension 2) s := rfl

theorem highest_action (s : ℕ) (q : CFSG.PrimePower) (a : fixedField q)
    (v : fixedSpace (s + 2) q) :
    fixedLinearHom (s + 2) q (highestInRelativeU s q a).val v =
      v + a • pairOperator (fixedQuadraticForm (s + 2) q).polarBilin
        (firstVector s q) (secondVector s q) v := by
  apply Subtype.ext
  change (fixedLinearHom (s + 2) q (highestInRelativeU s q a).val v).val =
    v.val + (a : q.Extension 2) •
      (((fixedQuadraticForm (s + 2) q).polarBilin (secondVector s q) v : fixedField q) •
          (firstVector s q).val -
        ((fixedQuadraticForm (s + 2) q).polarBilin (firstVector s q) v : fixedField q) •
          (secondVector s q).val)
  rw [fixedLinearHom_apply]
  change ((highestInRelativeU s q a).val.val : Mat (q.Extension 2) (s + 4)) *ᵥ v.val =
    v.val + (a : q.Extension 2) •
      ((((fixedQuadraticForm (s + 2) q).polarBilin (secondVector s q) v : fixedField q) : q.Extension 2) •
          (firstVector s q).val -
        (((fixedQuadraticForm (s + 2) q).polarBilin (firstVector s q) v : fixedField q) : q.Extension 2) •
          (secondVector s q).val)
  rw [fixedQuadraticForm_polar, fixedQuadraticForm_polar, firstVector_val, secondVector_val]
  have hv := LinearMap.congr_fun
    (CFSGOrthogonalDIndexPairOperator.highestRoot_displacement_pairOperator
      (q.Extension 2) s (a : q.Extension 2)) v.val
  simp only [Matrix.mulVecLin_apply, Matrix.sub_mulVec, Matrix.one_mulVec,
    LinearMap.smul_apply, pairOperator_apply] at hv
  have hm : ((highestInRelativeU s q a).val.val : Mat (q.Extension 2) (s + 4)) =
      ((CFSGOrthogonalDIndexPairOperator.highestRoot (q.Extension 2) s
        (a : q.Extension 2)).val : Mat (q.Extension 2) (s + 4)) := rfl
  rw [hm]
  simpa only [add_comm] using (sub_eq_iff_eq_add.mp hv)

theorem highest_displacement (s : ℕ) (q : CFSG.PrimePower) (a : fixedField q)
    (v : fixedSpace (s + 2) q) :
    fixedLinearHom (s + 2) q (highestInRelativeU s q a).val v - v =
      a • pairOperator (fixedQuadraticForm (s + 2) q).polarBilin
        (firstVector s q) (secondVector s q) v := by
  rw [highest_action, add_sub_cancel_left]

end SymmetricSubgroupAsymptotics.CFSGTwistedDHighestPairOperator
