import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCentralParameters
import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCentralRoot
import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryRootAxisPairing
import SymmetricSubgroupAsymptotics.CFSGTwistedAFirstBlock

/-! The off-diagonal parameter of a literal two-plane root star is an
ACTUAL radical element. Its middle vector is supported on the first
isotropic axis, so its norm vanishes in all fields and both parities.
The three supported matrix entries are displayed explicitly. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix

namespace SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
open CFSGTwistedANaturalMatrices CFSGTwistedAUpperUnipotent
open CFSGTwistedAUnitaryNaturalRadical CFSGTwistedAUnitaryUpperArrays
open CFSGTwistedAUnitaryParameters CFSGSerreOrdinaryTwists

def starPositive (s : ℕ) : Fin 2 → Fin (s + 4) := CFSGTwistedAFirstBlock.head s
def starNegative (s : ℕ) (i : Fin 2) : Fin (s + 4) := (starPositive s i).rev

theorem starPositive_injective (s : ℕ) : Function.Injective (starPositive s) := by
  intro i j h
  apply Fin.ext
  exact congrArg (fun x : Fin (s + 4) => x.val) h

theorem starNegative_injective (s : ℕ) : Function.Injective (starNegative s) := by
  intro i j h
  apply starPositive_injective s
  exact Fin.rev_injective h

theorem star_coordinates_disjoint (s : ℕ) (i j : Fin 2) : starNegative s i ≠ starPositive s j := by
  intro h
  have hv := congrArg (fun x : Fin (s + 4) => x.val) h
  have hi := i.isLt
  have hj := j.isLt
  simp only [starNegative, starPositive, CFSGTwistedAFirstBlock.head, Fin.val_rev, Fin.val_mk] at hv
  omega

theorem firstRow_starVector (q : CFSG.PrimePower) (s : ℕ) (d : q.Extension 2) :
    firstRow q (s + 1) (Pi.single (0 : Fin (s + 2)) d) =
      Pi.single (Fin.last (s + 1)) (parity q (s + 1) * definingFieldAutomorphism q 2 d) := by
  have hr : (0 : Fin (s + 2)).rev = Fin.last (s + 1) := by
    apply Fin.ext
    simp only [Fin.val_rev, Fin.val_zero, Fin.val_last]
    omega
  ext j
  rw [firstRow_single_entry]
  simp only [middleForm, Matrix.neg_apply, signedReversalUnit_apply, hr,
    signWeight, Fin.val_zero, pow_zero, Pi.single_apply]
  by_cases hj : j = Fin.last (s + 1)
  · subst j
    simp
  · simp [hj, Ne.symm hj]

theorem starVector_norm_zero (q : CFSG.PrimePower) (s : ℕ) (d : q.Extension 2) :
    hermitianNorm (definingFieldAutomorphism q 2) (middleForm q (s + 1))
      (Pi.single (0 : Fin (s + 2)) d) = 0 := by
  have hr : (0 : Fin (s + 2)).rev ≠ 0 := by
    intro h
    have hv := congrArg (fun x : Fin (s + 2) => x.val) h
    simp only [Fin.val_rev, Fin.val_zero] at hv
    omega
  have hmap : definingFieldAutomorphism q 2 ∘ (Pi.single (0 : Fin (s + 2)) d) =
      Pi.single 0 (definingFieldAutomorphism q 2 d) := by
    funext i
    by_cases hi : i = 0 <;> simp only [Function.comp_apply, Pi.single_apply,
      hi, if_true, if_false, map_zero]
  unfold hermitianNorm
  change dotProduct (definingFieldAutomorphism q 2 ∘ Pi.single (0 : Fin (s + 2)) d)
    (middleForm q (s + 1) *ᵥ Pi.single (0 : Fin (s + 2)) d) = 0
  rw [hmap, single_dotProduct]
  change definingFieldAutomorphism q 2 d *
    (dotProduct (middleForm q (s + 1) 0) (Pi.single (0 : Fin (s + 2)) d)) = 0
  rw [dotProduct_single]
  simp only [middleForm, Matrix.neg_apply, signedReversalUnit_apply, if_neg hr,
    neg_zero, zero_mul, mul_zero]

theorem starRadical_condition (q : CFSG.PrimePower) (s : ℕ) (d : q.Extension 2)
    (b : centralParameters q (s + 1)) :
    Condition q (s + 1) (Pi.single (0 : Fin (s + 2)) d) b.val := by
  change definingFieldAutomorphism q 2 b.val + parity q (s + 1) * b.val = _
  rw [starVector_norm_zero, neg_zero]
  exact b.property

def starRadicalFixed (q : CFSG.PrimePower) (s : ℕ) (d : q.Extension 2)
    (b : centralParameters q (s + 1)) : naturalFixed (s + 3) q :=
  upperFixedHom q (s + 3)
    (radicalElement q (s + 1) (Pi.single (0 : Fin (s + 2)) d) b.val (starRadical_condition q s d b))

private theorem upperArray_sparse {K J : Type*} [Field K] [Fintype J] [DecidableEq J]
    (i j : J) (w v b : K) :
    upperArray (Pi.single j w) (Pi.single i v) b =
      (1 : Matrix (Index J) (Index J) K) + Matrix.single (.inl ()) (.inr (.inr ())) b +
        Matrix.single (.inl ()) (.inr (.inl j)) w +
        Matrix.single (.inr (.inl i)) (.inr (.inr ())) v := by
  ext (u | (k | u)) (z | (l | z))
  all_goals try cases u
  all_goals try cases z
  all_goals simp [upperArray, Matrix.add_apply, Matrix.one_apply, Matrix.single_apply,
    Pi.single_apply, eq_comm]

private theorem reindex_single {K I J : Type*} [Field K] [DecidableEq I] [DecidableEq J]
    (e : I ≃ J) (i j : I) (a : K) :
    Matrix.reindex e e (Matrix.single i j a) = Matrix.single (e i) (e j) a := by
  ext x y
  obtain ⟨u, rfl⟩ := e.surjective x
  obtain ⟨v, rfl⟩ := e.surjective y
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.single_apply,
    Equiv.symm_apply_apply, e.injective.eq_iff]

theorem starRadicalFixed_matrix (q : CFSG.PrimePower) (s : ℕ) (d : q.Extension 2)
    (b : centralParameters q (s + 1)) :
    ((starRadicalFixed q s d b).val.val : Mat (q.Extension 2) (s + 3)) =
      1 + Matrix.single (starPositive s 0) (starNegative s 0) b.val +
        Matrix.single (starPositive s 0) (starNegative s 1)
          (parity q (s + 1) * definingFieldAutomorphism q 2 d) +
        Matrix.single (starPositive s 1) (starNegative s 0) d := by
  change ((radicalElement q (s + 1) (Pi.single (0 : Fin (s + 2)) d) b.val
    (starRadical_condition q s d b)).val.val : Mat (q.Extension 2) (s + 3)) = _
  rw [radicalElement_matrix, firstRow_starVector, upperArray_sparse]
  have h0 : splitEquiv (s + 1) (.inl ()) = starPositive s 0 := Fin.ext rfl
  have h1 : splitEquiv (s + 1) (.inr (.inl (0 : Fin (s + 2)))) = starPositive s 1 := Fin.ext rfl
  have hl : splitEquiv (s + 1) (.inr (.inr ())) = starNegative s 0 := by
    apply Fin.ext
    simp only [splitEquiv, Equiv.coe_fn_mk, splitIndex, starNegative, starPositive,
      CFSGTwistedAFirstBlock.head, Fin.val_mk, Fin.val_last, Fin.val_rev]
    omega
  have hp : splitEquiv (s + 1) (.inr (.inl (Fin.last (s + 1)))) = starNegative s 1 := by
    apply Fin.ext
    simp only [splitEquiv, Equiv.coe_fn_mk, splitIndex, starNegative, starPositive,
      CFSGTwistedAFirstBlock.head, Fin.val_mk, Fin.val_last, Fin.val_rev]
    omega
  change (Matrix.reindexAlgEquiv (q.Extension 2) (q.Extension 2) (splitEquiv (s + 1))) _ = _
  simp only [map_add, map_one, Matrix.reindexAlgEquiv_apply, reindex_single, h0, h1, hl, hp]

end SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
