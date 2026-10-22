import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryPairedAxisAction

/-! Actual endpoint-paired Weyl words supply an arbitrary nonzero
scalar on the first axis. In particular the construction does not demand
that an arbitrary extension-field scalar be a norm. All factors are in
the proved literal upper/opposite join. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix

namespace SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
open CFSGTwistedANaturalMatrices CFSGTwistedAUpperUnipotent

def pairedWeylParameter (q : CFSG.PrimePower) (s : ℕ) (a : q.Extension 2) :
    naturalFixed (s + 3) q :=
  endpointNaturalFixedPair q s false a * endpointNaturalFixedPair q s true (-a⁻¹) *
    endpointNaturalFixedPair q s false a

theorem pairedWeylParameter_mem_join (q : CFSG.PrimePower) (s : ℕ) (a : q.Extension 2) :
    (pairedWeylParameter q s a).val ∈ naturalUpperOppositeJoin q (s + 3) :=
  (naturalUpperOppositeJoin q (s + 3)).mul_mem
    ((naturalUpperOppositeJoin q (s + 3)).mul_mem
      (endpointPair_mem_join q s false a) (endpointPair_mem_join q s true (-a⁻¹)))
    (endpointPair_mem_join q s false a)

theorem pairedWeylParameter_axis_action (q : CFSG.PrimePower) (s : ℕ)
    (a b : q.Extension 2) (ha : a ≠ 0) (i : Fin 2) :
    ((pairedWeylParameter q s a).val.val : Mat (q.Extension 2) (s + 3)) *ᵥ
      Pi.single (CFSGTwistedAFirstBlock.head s i) b =
      if i = 0 then Pi.single (CFSGTwistedAFirstBlock.head s 1) (-a⁻¹ * b)
      else Pi.single (CFSGTwistedAFirstBlock.head s 0) (a * b) := by
  let p := CFSGTwistedAFirstBlock.head s (0 : Fin 2)
  let t := CFSGTwistedAFirstBlock.head s (1 : Fin 2)
  have hpt : p ≠ t := by
    intro he
    have hv := congrArg (fun j : Fin (s + 4) => j.val) he
    change (0 : ℕ) = 1 at hv
    omega
  have hp0 (c : q.Extension 2) :
      ((endpointNaturalFixedPair q s false a).val.val : Mat (q.Extension 2) (s + 3)) *ᵥ
        Pi.single p c = Pi.single p c := by
    simpa only [Bool.false_eq_true, if_false, if_true] using
      endpointPair_axis_action q s false a c 0
  have hp1 (c : q.Extension 2) :
      ((endpointNaturalFixedPair q s false a).val.val : Mat (q.Extension 2) (s + 3)) *ᵥ
        Pi.single t c = Pi.single t c + Pi.single p (a * c) := by
    simpa using endpointPair_axis_action q s false a c 1
  have hn0 (c : q.Extension 2) :
      ((endpointNaturalFixedPair q s true (-a⁻¹)).val.val : Mat (q.Extension 2) (s + 3)) *ᵥ
        Pi.single p c = Pi.single p c + Pi.single t ((-a⁻¹) * c) := by
    simpa only [if_true] using endpointPair_axis_action q s true (-a⁻¹) c 0
  have hn1 (c : q.Extension 2) :
      ((endpointNaturalFixedPair q s true (-a⁻¹)).val.val : Mat (q.Extension 2) (s + 3)) *ᵥ
        Pi.single t c = Pi.single t c := by
    simpa using endpointPair_axis_action q s true (-a⁻¹) c 1
  have hi : i = 0 ∨ i = 1 := by fin_cases i <;> simp
  rcases hi with rfl | rfl
  · change ((((endpointNaturalFixedPair q s false a).val.val : Mat (q.Extension 2) (s + 3)) *
        ((endpointNaturalFixedPair q s true (-a⁻¹)).val.val : Mat (q.Extension 2) (s + 3))) *
        ((endpointNaturalFixedPair q s false a).val.val : Mat (q.Extension 2) (s + 3))) *ᵥ
          Pi.single p b = Pi.single t (-a⁻¹ * b)
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hp0, hn0,
      Matrix.mulVec_add, hp0, hp1]
    ext j
    by_cases hjp : j = p
    · subst j
      simp [Pi.single_apply, Pi.add_apply, hpt, Ne.symm hpt] <;>
        field_simp [ha] <;> ring <;> simp
    · by_cases hjt : j = t
      · subst j
        simp [Pi.single_apply, Pi.add_apply, hpt, Ne.symm hpt]
      · simp [Pi.single_apply, Pi.add_apply, hjp, hjt, Ne.symm hjp, Ne.symm hjt]
  · change ((((endpointNaturalFixedPair q s false a).val.val : Mat (q.Extension 2) (s + 3)) *
        ((endpointNaturalFixedPair q s true (-a⁻¹)).val.val : Mat (q.Extension 2) (s + 3))) *
        ((endpointNaturalFixedPair q s false a).val.val : Mat (q.Extension 2) (s + 3))) *ᵥ
          Pi.single t b = Pi.single p (a * b)
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hp1,
      Matrix.mulVec_add, hn1, hn0, Matrix.mulVec_add, hp1,
      Matrix.mulVec_add, hp0, hp1]
    ext j
    by_cases hjp : j = p
    · subst j
      simp [Pi.single_apply, Pi.add_apply, hpt, Ne.symm hpt] <;>
        field_simp [ha] <;> ring <;> simp
    · by_cases hjt : j = t
      · subst j
        simp [Pi.single_apply, Pi.add_apply, hpt, Ne.symm hpt] <;>
          field_simp [ha] <;> ring <;> simp
      · simp [Pi.single_apply, Pi.add_apply, hjp, hjt, Ne.symm hjp, Ne.symm hjt]

def pairedTorus (q : CFSG.PrimePower) (s : ℕ) (a : q.Extension 2) :
    naturalFixed (s + 3) q :=
  pairedWeylParameter q s a * pairedWeylParameter q s (-1)

theorem pairedTorus_mem_join (q : CFSG.PrimePower) (s : ℕ) (a : q.Extension 2) :
    (pairedTorus q s a).val ∈ naturalUpperOppositeJoin q (s + 3) :=
  (naturalUpperOppositeJoin q (s + 3)).mul_mem
    (pairedWeylParameter_mem_join q s a) (pairedWeylParameter_mem_join q s (-1))

theorem pairedTorus_first_axis (q : CFSG.PrimePower) (s : ℕ)
    (a b : q.Extension 2) (ha : a ≠ 0) :
    ((pairedTorus q s a).val.val : Mat (q.Extension 2) (s + 3)) *ᵥ
      Pi.single (0 : Fin (s + 4)) b = Pi.single 0 (a * b) := by
  have h0 : CFSGTwistedAFirstBlock.head s (0 : Fin 2) = (0 : Fin (s + 4)) := Fin.ext rfl
  have hleft := pairedWeylParameter_axis_action q s (-1) b (neg_ne_zero.mpr one_ne_zero) 0
  have hright := pairedWeylParameter_axis_action q s a b ha 1
  simp only [if_true, inv_neg, inv_one, neg_neg, one_mul, h0] at hleft
  simp only [show (1 : Fin 2) ≠ 0 by decide, if_false, h0] at hright
  change (((pairedWeylParameter q s a).val.val : Mat (q.Extension 2) (s + 3)) *
    ((pairedWeylParameter q s (-1)).val.val : Mat (q.Extension 2) (s + 3))) *ᵥ _ = _
  rw [← Matrix.mulVec_mulVec, hleft, hright]

end SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
