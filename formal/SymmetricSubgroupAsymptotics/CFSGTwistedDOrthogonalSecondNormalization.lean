import SymmetricSubgroupAsymptotics.CFSGTwistedDAllRankHyperbolicPairs
import SymmetricSubgroupAsymptotics.CFSGTwistedDTailTwist
import SymmetricSubgroupAsymptotics.CFSGTwistedDAllRankChainLift
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTailQuadratic
import SymmetricSubgroupAsymptotics.CFSGTwistedDFixedVectorCoordinates
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexFlagVectors

/-! A singular vector orthogonal to the first positive axis and with
nonzero tail is normalized to the second positive axis by an actual
relative word fixing the first. This is the literal two-plane orbit
step, valid already when the ambient relative rank is four. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGTwistedDOrthogonalSecondNormalization
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDGenerationRootArrays
open CFSGOrthogonalDIndexTailCoordinates CFSGOrthogonalDIndexBundledQuadratic
open CFSGTwistedDRelativeElementaryGroup CFSGTwistedDRelativeTailEmbedding
open CFSGTwistedDNaturalQuadraticTwist CFSGSerreOrdinaryTwists
open CFSGTwistedDA2MatrixWitness CFSGTwistedA2FixedField
open CFSGOrthogonalDGenerationForkTorus CFSGOrthogonalDIndexFlagVectors

theorem chain_array_clear (K : Type) [Field K] (r : ℕ)
    (i j : Fin r) (hij : i ≠ j) (c : K) :
    chainArray i j (-c) *ᵥ
        (c • Pi.single (Sum.inl i) 1 + Pi.single (Sum.inl j) 1) =
      (Pi.single (Sum.inl j) 1 : Index r → K) := by
  funext x
  simp only [chainArray, Matrix.add_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec,
    Matrix.single_mulVec, Pi.add_apply, Pi.sub_apply, Pi.smul_apply,
    Function.update_apply, Pi.zero_apply, Pi.single_apply, smul_eq_mul]
  simp only [Sum.inl.injEq, Sum.inr_ne_inl, if_false, if_true,
    Ne.symm hij, mul_zero, add_zero, zero_add, mul_one]
  split_ifs <;> ring

theorem chain_array_fixes (K : Type) [Field K] (r : ℕ)
    (i j : Fin r) (hij : i ≠ j) (c : K) :
    chainArray i j c *ᵥ (Pi.single (Sum.inl i) 1 : Index r → K) =
      Pi.single (Sum.inl i) 1 := by
  rw [Matrix.mulVec_single_one]
  funext x
  simp [chainArray, Matrix.col_apply, Matrix.single_apply, Matrix.one_apply,
    Pi.single_apply, hij, Ne.symm hij, eq_comm]

theorem exists_normalize_second (s : ℕ) (q : CFSG.PrimePower)
    (v : Index (s + 4) → q.Extension 2)
    (hv : vectorTwist (q.Extension 2) (s + 2) (definingFieldAutomorphism q 2) v = v)
    (hQ : splitQuadraticForm (q.Extension 2) (s + 4) v = 0)
    (hn : v (Sum.inr 0) = 0)
    (ht : tailRestriction (q.Extension 2) (s + 3) v ≠ 0) :
    ∃ u : relativeRootGroup (s + 2) q,
      (u.val : Mat (q.Extension 2) (s + 4)) *ᵥ Pi.single (Sum.inl 0) 1 =
          Pi.single (Sum.inl 0) 1 ∧
      (u.val : Mat (q.Extension 2) (s + 4)) *ᵥ v =
          Pi.single (Sum.inl (secondIndex s)) 1 := by
  have htf : vectorTwist (q.Extension 2) (s + 1) (definingFieldAutomorphism q 2)
      (tailRestriction (q.Extension 2) (s + 3) v) =
      tailRestriction (q.Extension 2) (s + 3) v := by
    change vectorTwist (q.Extension 2) (s + 1) (definingFieldAutomorphism q 2)
      (v ∘ tailIndex (s + 3)) = v ∘ tailIndex (s + 3)
    rw [CFSGTwistedDTailTwist.vectorTwist_tail, hv]
  have htQ : splitQuadraticForm (q.Extension 2) (s + 3)
      (tailRestriction (q.Extension 2) (s + 3) v) = 0 := by
    rw [splitQuadraticForm_apply, ← splitQ_tail_of_negative_head_zero _ _ v hn,
      ← splitQuadraticForm_apply]
    exact hQ
  obtain ⟨a, ha⟩ := CFSGTwistedDAllRankSingularOrbit.exists_normalize_all
    (s + 1) q _ htf htQ ht
  let b := tailRelativeHom (s + 1) q a
  let w := (b.val : Mat (q.Extension 2) (s + 4)) *ᵥ v
  have hw : tailRestriction (q.Extension 2) (s + 3) w = Pi.single (Sum.inl 0) 1 := by
    exact (tail_action (s + 1) q a v).trans ha
  have hwn : w (Sum.inr 0) = 0 := (head_negative (s + 1) q a v).trans hn
  have hwp : w (Sum.inl 0) = v (Sum.inl 0) := head_positive (s + 1) q a v
  have hform : w = v (Sum.inl 0) • Pi.single (Sum.inl 0) 1 +
      Pi.single (Sum.inl (secondIndex s)) 1 := by
    have h := vector_eq_first_add_tail_basis (q.Extension 2) (s + 2) w hw hwn
    rw [hwp] at h
    exact h
  have h0 : (0 : Fin (s + 4)) ≠ last (s + 2) := by
    intro h
    have hh := congrArg Fin.val h
    change 0 = s + 3 at hh
    omega
  let c : fixedField q := ⟨v (Sum.inl 0),
    CFSGTwistedDFixedVectorCoordinates.positive_fixed _ _ _ v hv 0 h0⟩
  let i : Fin (s + 3) := 0
  let j : Fin (s + 3) := ⟨1, by omega⟩
  have hij : i ≠ j := by
    intro h
    have hh := congrArg Fin.val h
    change 0 = 1 at hh
    omega
  let d : relativeRootGroup (s + 2) q :=
    ⟨(chain (q.Extension 2) (s + 4) i.castSucc j.castSucc
      ((Fin.castSucc_injective (s + 3)).ne hij) ((-c : fixedField q) : q.Extension 2)).val,
      CFSGTwistedDAllRankChainLift.chain_mem (s + 2) q i j hij (-c)⟩
  have hd : (d.val : Mat (q.Extension 2) (s + 4)) =
      chainArray (0 : Fin (s + 4)) (secondIndex s) (-v (Sum.inl 0)) := by
    rw [show (d.val : Mat (q.Extension 2) (s + 4)) =
      ((chain (q.Extension 2) (s + 4) i.castSucc j.castSucc
        ((Fin.castSucc_injective (s + 3)).ne hij) ((-c : fixedField q) : q.Extension 2)).val :
          Mat (q.Extension 2) (s + 4)) from rfl,
      CFSGTwistedDRetainedForkRoots.chain_val]
    rfl
  have hbfix : (b.val : Mat (q.Extension 2) (s + 4)) *ᵥ Pi.single (Sum.inl 0) 1 =
      Pi.single (Sum.inl 0) 1 :=
    tailElementaryHom_fixes_first_positive (q.Extension 2) (s + 3) (by omega)
      ⟨a.val, relativeRootGroup_le_elementary (s + 1) q a.property⟩
  refine ⟨d * b, ?_, ?_⟩
  · change ((d.val : Mat (q.Extension 2) (s + 4)) *
      (b.val : Mat (q.Extension 2) (s + 4))) *ᵥ _ = _
    rw [← Matrix.mulVec_mulVec, hbfix, hd]
    exact chain_array_fixes _ _ _ _ (zero_ne_second s) _
  · change ((d.val : Mat (q.Extension 2) (s + 4)) *
      (b.val : Mat (q.Extension 2) (s + 4))) *ᵥ v = _
    rw [← Matrix.mulVec_mulVec]
    change (d.val : Mat (q.Extension 2) (s + 4)) *ᵥ w = _
    rw [hd, hform]
    exact chain_array_clear _ _ _ _ (zero_ne_second s) _

end SymmetricSubgroupAsymptotics.CFSGTwistedDOrthogonalSecondNormalization
