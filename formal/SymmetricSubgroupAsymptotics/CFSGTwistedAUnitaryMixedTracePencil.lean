import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryPairReciprocity
import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryOpposedLocalFields

/-! In the four-dimensional coordinate half-sum of the natural rank-four
space, every separating mixed pencil has two distinct finite orthogonal
mixed members. The actual signed-trace equation supplies them also at
q=2; together with the point at infinity these are three fixed rays. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
open CFSGTwistedANaturalMatrices CFSGSerreOrdinaryTwists CFSGTwistedAUnitaryParameters

theorem unitaryRankFour_pair_reciprocal (q : CFSG.PrimePower)
    (v w : Fin 5 → q.Extension 2) :
    unitaryNaturalPair q 4 v w = definingFieldAutomorphism q 2 (unitaryNaturalPair q 4 w v) := by
  have he : (-1 : q.Extension 2)^4 = 1 := by ring
  simpa only [he, one_mul] using unitaryNaturalPair_signed_reciprocal q 4 v w

private theorem pair_add_left (q : CFSG.PrimePower) (v w a : Fin 5 → q.Extension 2) :
    unitaryNaturalPair q 4 (v + w) a = unitaryNaturalPair q 4 v a + unitaryNaturalPair q 4 w a :=
  hermitianPair_add_left _ _ v w a

private theorem pair_add_right (q : CFSG.PrimePower) (v w a : Fin 5 → q.Extension 2) :
    unitaryNaturalPair q 4 v (w + a) = unitaryNaturalPair q 4 v w + unitaryNaturalPair q 4 v a :=
  hermitianPair_add_right _ _ v w a

private theorem pair_smul (q : CFSG.PrimePower) (a b : q.Extension 2) (v w : Fin 5 → q.Extension 2) :
    unitaryNaturalPair q 4 (a • v) (b • w) =
      definingFieldAutomorphism q 2 a * b * unitaryNaturalPair q 4 v w :=
  hermitianPair_smul _ _ a b v w

theorem exists_unitaryRankFour_two_mixed_pencil_parameters (q : CFSG.PrimePower)
    (x y u z : Fin 5 → q.Extension 2)
    (hx : x ∈ unitaryStandardSingularSpace q 4) (hu : u ∈ unitaryStandardSingularSpace q 4)
    (hy : y ∈ unitaryOppositeSingularSpace q 4) (hz : z ∈ unitaryOppositeSingularSpace q 4)
    (hnorm : unitaryNaturalPair q 4 (x + y) (x + y) = 0)
    (hzu : unitaryNaturalPair q 4 z u = 0)
    (hxz : unitaryNaturalPair q 4 x z = -unitaryNaturalPair q 4 y u)
    (hd : unitaryNaturalPair q 4 y u ≠ 0) :
    ∃ t t' : q.Extension 2, t ≠ t' ∧
      unitaryNaturalPair q 4 (y + t • z) (x + t • u) = 0 ∧
      unitaryNaturalPair q 4 (y + t' • z) (x + t' • u) = 0 := by
  let sig := definingFieldAutomorphism q 2
  let c := unitaryNaturalPair q 4 y x
  let d := unitaryNaturalPair q 4 y u
  have hc : sig c = -c := by
    rw [pair_add_left, pair_add_right, pair_add_right] at hnorm
    -- The diagonal entries vanish in their own literal coordinate halves.
    have hxx := unitaryStandardSingularSpace_pair_zero q 4 x hx x hx
    have hyy := unitaryOppositeSingularSpace_pair_zero q 4 y y hy hy
    rw [hxx, hyy, zero_add, add_zero, unitaryRankFour_pair_reciprocal] at hnorm
    exact add_eq_zero_iff_eq_neg.mp hnorm
  obtain ⟨b, hb⟩ := exists_sigma_sub_eq q c hc
  let t := b / d
  let t' := (b + 1) / d
  have htd : t * d = b := div_mul_cancel₀ b hd
  have ht'd : t' * d = b + 1 := div_mul_cancel₀ (b + 1) hd
  have hzxf : unitaryNaturalPair q 4 z x = -sig d := by
    rw [unitaryRankFour_pair_reciprocal, hxz, map_neg]
  have hformula (a : q.Extension 2) :
      unitaryNaturalPair q 4 (y + a • z) (x + a • u) = c + a * d - sig (a * d) := by
    have hys := pair_smul q 1 a y u
    have hzs := pair_smul q a 1 z x
    have hzsu := pair_smul q a a z u
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
