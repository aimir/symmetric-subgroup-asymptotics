import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryMiddleUpper
import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryRegularArrays
import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCentralDerived
import SymmetricSubgroupAsymptotics.CFSGTwistedA2UnitRootTwist

/-! A genuine regular upper element in every original defining-fixed
natural upper group. Every adjacent entry is nonzero. The construction
uses the actual trace-solvable outer radical and literal middle block;
it includes field order two and assumes no whole-unitary equality. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix

namespace SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
open CFSGTwistedANaturalMatrices CFSGTwistedAUpperUnipotent
open CFSGTwistedAUnitaryUpperArrays CFSGTwistedAUnitaryNaturalRadical
open CFSGSerreSquareZeroMatrix CFSGSerreOrdinaryTwists

theorem firstRow_last_one_zero (q : CFSG.PrimePower) (s : ℕ) :
    firstRow q s (Pi.single (Fin.last s) 1) 0 = 1 := by
  have hl : (Fin.last s).rev = (0 : Fin (s + 1)) := by
    apply Fin.ext
    simp [Fin.rev]
  rw [firstRow_single_entry]
  simp only [middleForm, Matrix.neg_apply, signedReversalUnit_apply, hl, if_true,
    signWeight, Fin.val_last, map_one, mul_one]
  change (-((-1 : q.Extension 2) ^ s)) * (-((-1 : q.Extension 2) ^ s)) = 1
  rw [neg_mul_neg, ← mul_pow]
  simp

theorem exists_regular_upper_one (q : CFSG.PrimePower) :
    ∃ u : naturalUnipotent 1 q, ∀ i : Fin 1,
      (u.val.val : Mat (q.Extension 2) 1) i.castSucc i.succ ≠ 0 := by
  let a : NaturalElementary (q.Extension 2) 1 :=
    elementaryRoot (q.Extension 2) (naturalRootUnit (q.Extension 2) 1) false 0 1
  have hm : (a.val : Mat (q.Extension 2) 1) =
      1 + Matrix.single (0 : Fin 2) 1 1 := by
    change 1 + (1 : q.Extension 2) • positive (q.Extension 2) 1 0 = _
    rw [one_smul]
    rfl
  have hu : naturalToSpecialLinear (q.Extension 2) 1 a ∈
      CFSGUpperUnitriangular.upperUnitriangular (q.Extension 2) 2 := by
    constructor
    · intro i j hij
      change (a.val : Mat (q.Extension 2) 1) i j = 0
      rw [hm]
      fin_cases i <;> fin_cases j
      all_goals norm_num [Matrix.add_apply, Matrix.single_apply, Matrix.one_apply,
        Fin.ext_iff] at *
    · intro i
      change (a.val : Mat (q.Extension 2) 1) i i = 1
      rw [hm]
      fin_cases i <;> norm_num [Matrix.add_apply, Matrix.single_apply, Matrix.one_apply,
        Fin.ext_iff]
  have hf : a ∈ naturalFixed 1 q := by
    change diagramFieldUnitHom (q.Extension 2) 1 (definingFieldAutomorphism q 2).toRingHom
      (naturalRootUnit (q.Extension 2) 1 false 0 1) = _
    have hrev : (0 : Fin 1).rev = 0 := Subsingleton.elim _ _
    simpa only [hrev, map_one] using CFSGTwistedA2UnitRootTwist.simpleUnit_twist
      (q.Extension 2) (definingFieldAutomorphism q 2) 1 false 0 1
  refine ⟨⟨a, hu, hf⟩, ?_⟩
  intro i
  fin_cases i
  change (a.val : Mat (q.Extension 2) 1) 0 1 ≠ 0
  rw [hm]
  norm_num [Matrix.add_apply, Matrix.single_apply, Matrix.one_apply, Fin.ext_iff]

theorem exists_regular_upper_step (q : CFSG.PrimePower) (s : ℕ)
    (a : naturalUnipotent s q)
    (ha : ∀ i : Fin s, (a.val.val : Mat (q.Extension 2) s) i.castSucc i.succ ≠ 0) :
    ∃ u : naturalUnipotent (s + 2) q, ∀ i : Fin (s + 2),
      (u.val.val : Mat (q.Extension 2) (s + 2)) i.castSucc i.succ ≠ 0 := by
  let v : Fin (s + 1) → q.Extension 2 := Pi.single (Fin.last s) 1
  obtain ⟨b, hb⟩ := condition_exists q s v
  let u := radicalElement q s v b hb * middleUnipotentHom q s a
  let e := Matrix.reindexAlgEquiv (q.Extension 2) (q.Extension 2) (splitEquiv s)
  have hu : (u.val.val : Mat (q.Extension 2) (s + 2)) =
      Matrix.reindex (splitEquiv s) (splitEquiv s)
        (upperMiddleArray (firstRow q s v ᵥ* (a.val.val : Mat (q.Extension 2) s))
          (a.val.val : Mat (q.Extension 2) s) v b) := by
    change e (upperArray (firstRow q s v) v b) * e (middleArray (a.val.val : Mat (q.Extension 2) s)) = _
    rw [← map_mul, upperArray_mul_middleArray]
    rfl
  refine ⟨u, ?_⟩
  intro i
  rw [hu]
  apply upperMiddleArray_regular s _ _ v b ?_ ?_ ha i
  · have hhead : (firstRow q s v ᵥ* (a.val.val : Mat (q.Extension 2) s)) 0 = firstRow q s v 0 :=
      vecMul_zero_of_upper s (a.val.val : Mat (q.Extension 2) s)
        a.property.1.1 a.property.1.2 (firstRow q s v)
    rw [hhead]
    have hw := firstRow_last_one_zero q s
    change firstRow q s (Pi.single (Fin.last s) 1) 0 ≠ 0
    rw [hw]
    exact one_ne_zero
  · change (Pi.single (Fin.last s) (1 : q.Extension 2) : Fin (s + 1) → q.Extension 2) (Fin.last s) ≠ 0
    simp

theorem exists_regular_upper (q : CFSG.PrimePower) (r : ℕ) :
    ∃ u : naturalUnipotent r q, ∀ i : Fin r,
      (u.val.val : Mat (q.Extension 2) r) i.castSucc i.succ ≠ 0 := by
  induction r using Nat.strong_induction_on with
  | h r ih =>
    cases r with
    | zero => exact ⟨1, fun i => Fin.elim0 i⟩
    | succ r =>
      cases r with
      | zero => exact exists_regular_upper_one q
      | succ s =>
        obtain ⟨u, hu⟩ := ih s (by omega)
        exact exists_regular_upper_step q s u hu

end SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
