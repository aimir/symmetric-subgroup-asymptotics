import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryPairReciprocity
import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryOpposedLocalFields

/-! In every odd-dimensional signed unitary coordinate space, every separating mixed pencil has two distinct finite orthogonal
mixed members. The actual signed-trace equation supplies them also at
q=2; together with the point at infinity these are three fixed rays. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
open CFSGTwistedANaturalMatrices CFSGSerreOrdinaryTwists CFSGTwistedAUnitaryParameters

theorem unitary_oddSpace_pair_reciprocal (q : CFSG.PrimePower) (r : ℕ) (hr : Even r)
    (v w : Fin (r+1) → q.Extension 2) :
    unitaryNaturalPair q r v w = definingFieldAutomorphism q 2 (unitaryNaturalPair q r w v) := by
  have he : (-1 : q.Extension 2)^r = 1 := hr.neg_one_pow
  simpa only [he, one_mul] using unitaryNaturalPair_signed_reciprocal q r v w

private theorem pair_add_left (q : CFSG.PrimePower) (r : ℕ) (v w a : Fin (r+1) → q.Extension 2) :
    unitaryNaturalPair q r (v + w) a = unitaryNaturalPair q r v a + unitaryNaturalPair q r w a :=
  hermitianPair_add_left _ _ v w a

private theorem pair_add_right (q : CFSG.PrimePower) (r : ℕ) (v w a : Fin (r+1) → q.Extension 2) :
    unitaryNaturalPair q r v (w + a) = unitaryNaturalPair q r v w + unitaryNaturalPair q r v a :=
  hermitianPair_add_right _ _ v w a

private theorem pair_smul (q : CFSG.PrimePower) (r : ℕ) (a b : q.Extension 2) (v w : Fin (r+1) → q.Extension 2) :
    unitaryNaturalPair q r (a • v) (b • w) =
      definingFieldAutomorphism q 2 a * b * unitaryNaturalPair q r v w :=
  hermitianPair_smul _ _ a b v w

theorem exists_unitary_two_mixed_pencil_parameters (q : CFSG.PrimePower) (r : ℕ) (hr : Even r)
    (x y u z : Fin (r+1) → q.Extension 2)
    (hx : x ∈ unitaryStandardSingularSpace q r) (hu : u ∈ unitaryStandardSingularSpace q r)
    (hy : y ∈ unitaryOppositeSingularSpace q r) (hz : z ∈ unitaryOppositeSingularSpace q r)
    (hnorm : unitaryNaturalPair q r (x + y) (x + y) = 0)
    (hzu : unitaryNaturalPair q r z u = 0)
    (hxz : unitaryNaturalPair q r x z = -unitaryNaturalPair q r y u)
    (hd : unitaryNaturalPair q r y u ≠ 0) :
    ∃ t t' : q.Extension 2, t ≠ t' ∧
      unitaryNaturalPair q r (y + t • z) (x + t • u) = 0 ∧
      unitaryNaturalPair q r (y + t' • z) (x + t' • u) = 0 := by
  let sig := definingFieldAutomorphism q 2
  let c := unitaryNaturalPair q r y x
  let d := unitaryNaturalPair q r y u
  have hc : sig c = -c := by
    rw [pair_add_left, pair_add_right, pair_add_right] at hnorm
    -- The diagonal entries vanish in their own literal coordinate halves.
    have hxx := unitaryStandardSingularSpace_pair_zero q r x hx x hx
    have hyy := unitaryOppositeSingularSpace_pair_zero q r y y hy hy
    rw [hxx, hyy, zero_add, add_zero, unitary_oddSpace_pair_reciprocal q r hr] at hnorm
    exact add_eq_zero_iff_eq_neg.mp hnorm
  obtain ⟨b, hb⟩ := exists_sigma_sub_eq q c hc
  let t := b / d
  let t' := (b + 1) / d
  have htd : t * d = b := div_mul_cancel₀ b hd
  have ht'd : t' * d = b + 1 := div_mul_cancel₀ (b + 1) hd
  have hzxf : unitaryNaturalPair q r z x = -sig d := by
    rw [unitary_oddSpace_pair_reciprocal q r hr, hxz, map_neg]
  have hformula (a : q.Extension 2) :
      unitaryNaturalPair q r (y + a • z) (x + a • u) = c + a * d - sig (a * d) := by
    have hys := pair_smul q r 1 a y u
    have hzs := pair_smul q r a 1 z x
    have hzsu := pair_smul q r a a z u
    simp only [one_smul, map_one, one_mul, mul_one, hzu, mul_zero] at hys hzs hzsu
    rw [pair_add_left, pair_add_right, pair_add_right, hys, hzs, hzsu,
      hzxf, map_mul]
    change c + a * d + (sig a * -sig d + 0) = c + a * d - sig a * sig d
    ring
  refine ⟨t, t', ?_, ?_, ?_⟩
  · intro he
    have hh := congrArg (fun a : q.Extension 2 => a * d) he
    dsimp only at hh
    rw [htd, ht'd] at hh
    have h01 : (0 : q.Extension 2) = 1 := add_left_cancel (by simpa only [add_zero] using hh)
    exact zero_ne_one h01
  · rw [hformula, htd]
    change c + b - definingFieldAutomorphism q 2 b = 0
    rw [← hb]
    ring
  · rw [hformula, ht'd]
    change c + (b + 1) - definingFieldAutomorphism q 2 (b + 1) = 0
    rw [map_add, map_one, ← hb]
    ring

end SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
