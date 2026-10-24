import SymmetricSubgroupAsymptotics.CFSGUnitaryNaturalNormOrbit
import SymmetricSubgroupAsymptotics.CFSGUnitarySignedTraceSliceCardinality
import SymmetricSubgroupAsymptotics.CFSGUnitaryMatrixCardinalityBounds

/-! A genuine trace slice injects into every nonzero actual natural
SU orbit. Only literal fixed matrices are used; vector dimension is at
least three and no dimension-two transitivity is asserted. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix

namespace SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
open CFSGTwistedANaturalMatrices CFSGTwistedAUpperUnipotent
open CFSGTwistedAUnitaryParameters CFSGTwistedAUnitaryUpperArrays
open CFSGTwistedAUnitaryNaturalRadical CFSGSerreOrdinaryTwists
open CFSGHermitianHyperbolicCompression CFSGUnitarySignedTraceSliceCardinality

private def normLevelSplit (q : CFSG.PrimePower) (s : ℕ)
    (p : (q.Extension 2 × (Fin (s + 1) → q.Extension 2)) × q.Extension 2) :
    Index (Fin (s + 1)) → q.Extension 2
  | .inl _ => p.1.1
  | .inr (.inl i) => p.1.2 i
  | .inr (.inr _) => p.2

def unitaryNormLevelVector (q : CFSG.PrimePower) (s : ℕ)
    (p : (q.Extension 2 × (Fin (s + 1) → q.Extension 2)) × q.Extension 2) :
    Fin (s + 3) → q.Extension 2 :=
  (unitarySplitLinearEquiv q s).symm (normLevelSplit q s p)

private theorem normLevelVector_split (q : CFSG.PrimePower) (s : ℕ)
    (p : (q.Extension 2 × (Fin (s + 1) → q.Extension 2)) × q.Extension 2) :
    unitarySplitLinearEquiv q s (unitaryNormLevelVector q s p) = normLevelSplit q s p :=
  (unitarySplitLinearEquiv q s).apply_symm_apply _

theorem unitaryNormLevelVector_first (q : CFSG.PrimePower) (s : ℕ)
    (p : (q.Extension 2 × (Fin (s + 1) → q.Extension 2)) × q.Extension 2) :
    unitaryNormLevelVector q s p 0 = p.1.1 := by
  have h := congrFun (normLevelVector_split q s p) (.inl ())
  exact h

theorem unitaryNormLevelVector_injective (q : CFSG.PrimePower) (s : ℕ) :
    Function.Injective (unitaryNormLevelVector q s) := by
  intro p t he
  have h := congrArg (unitarySplitLinearEquiv q s) he
  rw [normLevelVector_split, normLevelVector_split] at h
  have hx : p.1.1 = t.1.1 := congrFun h (.inl ())
  have hy : p.2 = t.2 := congrFun h (.inr (.inr ()))
  have hw : p.1.2 = t.1.2 := funext (fun i => congrFun h (.inr (.inl i)))
  exact Prod.ext (Prod.ext hx hw) hy

theorem unitaryNormLevelVector_norm (q : CFSG.PrimePower) (s : ℕ)
    (p : (q.Extension 2 × (Fin (s + 1) → q.Extension 2)) × q.Extension 2) :
    unitaryNaturalPair q (s + 2) (unitaryNormLevelVector q s p) (unitaryNormLevelVector q s p) =
      definingFieldAutomorphism q 2 p.1.1 * p.2 +
        parity q s * definingFieldAutomorphism q 2 p.2 * p.1.1 +
          hermitianNorm (definingFieldAutomorphism q 2) (middleForm q s) p.1.2 := by
  rw [unitaryNaturalPair_split]
  simp only [normLevelVector_split, block_pair]
  change definingFieldAutomorphism q 2 p.1.1 * p.2 +
      hermitianNorm (definingFieldAutomorphism q 2) (middleForm q s) p.1.2 +
        parity q s * definingFieldAutomorphism q 2 p.2 * p.1.1 = _
  ring

theorem natural_unitary_norm_sigma (q : CFSG.PrimePower) (s : ℕ)
    (v : Fin (s + 3) → q.Extension 2) :
    definingFieldAutomorphism q 2 (unitaryNaturalPair q (s + 2) v v) =
      parity q s * unitaryNaturalPair q (s + 2) v v := by
  have hs : (-1 : q.Extension 2) ^ (s + 2) = parity q s := by
    simp [parity, pow_add]
  have h := hermitianNorm_sigma (definingFieldAutomorphism q 2)
    (fun x => extension_two_pow_twice q x) ((-1 : q.Extension 2) ^ (s + 2))
    (signedReversalUnit (q.Extension 2) (s + 2) : Mat (q.Extension 2) (s + 2))
    (signedReversal_hermitian q (s + 2)) v
  change definingFieldAutomorphism q 2 (unitaryNaturalPair q (s + 2) v v) =
    (-1 : q.Extension 2) ^ (s + 2) * unitaryNaturalPair q (s + 2) v v at h
  simpa only [hs] using h

def unitaryVectorOrbit (q : CFSG.PrimePower) (s : ℕ) (v : Fin (s + 3) → q.Extension 2) :
    Set (Fin (s + 3) → q.Extension 2) :=
  {w | ∃ g : naturalFixed (s + 2) q, (g.val.val : Mat (q.Extension 2) (s + 2)) *ᵥ v = w}

theorem trace_slice_le_unitaryVectorOrbit (q : CFSG.PrimePower) (s : ℕ)
    (v : Fin (s + 3) → q.Extension 2) (hv : v ≠ 0) :
    (q.order ^ 2 - 1) * q.order ^ (2 * s + 3) ≤ Nat.card (unitaryVectorOrbit q s v) := by
  let Q := hermitianNorm (definingFieldAutomorphism q 2) (middleForm q s)
  let c := unitaryNaturalPair q (s + 2) v v
  let S := traceSlice q s Q c
  have hQ (w : Fin (s + 1) → q.Extension 2) :
      definingFieldAutomorphism q 2 (Q w) = parity q s * Q w :=
    hermitianNorm_sigma (definingFieldAutomorphism q 2)
      (fun a => extension_two_pow_twice q a) (parity q s) (middleForm q s)
      (middleForm_hermitian q s) w
  let f : S → unitaryVectorOrbit q s v := fun p =>
    ⟨unitaryNormLevelVector q s p.val, by
      have hp : unitaryNormLevelVector q s p.val ≠ 0 := by
        intro he
        apply p.property.1
        have hfirst := congrFun he 0
        rw [unitaryNormLevelVector_first] at hfirst
        exact hfirst
      have hn : unitaryNaturalPair q (s + 2) (unitaryNormLevelVector q s p.val)
          (unitaryNormLevelVector q s p.val) = c :=
        (unitaryNormLevelVector_norm q s p.val).trans p.property.2
      exact exists_natural_map_of_same_norm q s v (unitaryNormLevelVector q s p.val) hv hp hn.symm⟩
  have hf : Function.Injective f := by
    intro p t he
    apply Subtype.ext
    apply unitaryNormLevelVector_injective q s
    exact congrArg (fun w : unitaryVectorOrbit q s v => w.val) he
  have hs := card_traceSlice_lower q s (Fin (s + 1) → q.Extension 2) Q hQ c
    (natural_unitary_norm_sigma q s v)
  have hW : Nat.card (Fin (s + 1) → q.Extension 2) = q.order ^ (2 * (s + 1)) := by
    rw [Nat.card_fun, Nat.card_fin, extension_two_card, ← pow_mul]
  have hp : (q.order ^ 2 - 1) * q.order ^ (2 * (s + 1)) * q.order =
      (q.order ^ 2 - 1) * q.order ^ (2 * s + 3) := by
    rw [mul_assoc, ← pow_succ]
    congr 1
  rw [hW, hp] at hs
  exact hs.trans (Nat.card_le_card_of_injective f hf)

end SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
