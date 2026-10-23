import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryStarHermitianMap

/-! The explicit inverse Hermitian coefficient map. Every Hermitian
matrix gives genuine signed central diagonal parameters and an arbitrary
quadratic-field off-diagonal parameter. This completes an actual additive
equivalence, rather than assuming surjectivity or a form identification. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
open CFSGTwistedAUnitaryNaturalRadical CFSGSerreOrdinaryTwists

theorem star_central_mul_fixed (q : CFSG.PrimePower) (s : ℕ)
    (t : q.Extension 2) (htc : t ∈ centralParameters q (s + 1))
    (a : q.Extension 2) (ha : definingFieldAutomorphism q 2 a = a) :
    t * a ∈ centralParameters q (s + 1) := by
  change definingFieldAutomorphism q 2 (t * a) + parity q (s + 1) * (t * a) = 0
  rw [map_mul, ha, centralParameter_sigma q (s + 1) t htc]
  ring

def starHermitianInverse (q : CFSG.PrimePower) (s : ℕ)
    (t : q.Extension 2) (htc : t ∈ centralParameters q (s + 1))
    (A : CFSGHermitianTwoByTwoRankOne.parameters (definingFieldAutomorphism q 2)) :
    StarParameters q s :=
  (⟨t * A.val 0 0, star_central_mul_fixed q s t htc _ (A.property 0 0)⟩,
    t * A.val 1 0,
    ⟨-(t * A.val 1 1), (centralParameters q (s + 1)).neg_mem
      (star_central_mul_fixed q s t htc _ (A.property 1 1))⟩)

theorem starHermitianInverse_left (q : CFSG.PrimePower) (s : ℕ)
    (t : q.Extension 2) (ht : t ≠ 0) (htc : t ∈ centralParameters q (s + 1))
    (x : StarParameters q s) :
    starHermitianInverse q s t htc (starHermitianHom q s t ht htc x) = x := by
  apply Prod.ext
  · apply Subtype.ext
    change t * ((x.1.val / t) * 1) = x.1.val
    field_simp [ht]
  · apply Prod.ext
    · change t * ((x.2.1 / t) * 1) = x.2.1
      field_simp [ht]
    · apply Subtype.ext
      change -(t * ((x.2.2.val / t) * (-1))) = x.2.2.val
      field_simp [ht]

theorem starHermitianInverse_right (q : CFSG.PrimePower) (s : ℕ)
    (t : q.Extension 2) (ht : t ≠ 0) (htc : t ∈ centralParameters q (s + 1))
    (A : CFSGHermitianTwoByTwoRankOne.parameters (definingFieldAutomorphism q 2)) :
    starHermitianHom q s t ht htc (starHermitianInverse q s t htc A) = A := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j
  · change ((t * A.val 0 0) / t) * 1 = A.val 0 0
    field_simp [ht]
  · change ((parity q (s + 1) * definingFieldAutomorphism q 2 (t * A.val 1 0)) / t) * (-1) = A.val 0 1
    rw [map_mul, centralParameter_sigma q (s + 1) t htc, A.property 0 1]
    rcases neg_one_pow_eq_or (q.Extension 2) (s + 1) with he | he
    · have he' : parity q (s + 1) = 1 := he
      rw [he']
      field_simp [ht] <;> ring
    · have he' : parity q (s + 1) = -1 := he
      rw [he']
      field_simp [ht] <;> ring
  · change ((t * A.val 1 0) / t) * 1 = A.val 1 0
    field_simp [ht]
  · change ((-(t * A.val 1 1)) / t) * (-1) = A.val 1 1
    field_simp [ht]

def starHermitianEquiv (q : CFSG.PrimePower) (s : ℕ)
    (t : q.Extension 2) (ht : t ≠ 0) (htc : t ∈ centralParameters q (s + 1)) :
    StarParameters q s ≃+
      CFSGHermitianTwoByTwoRankOne.parameters (definingFieldAutomorphism q 2) where
  toFun := starHermitianHom q s t ht htc
  invFun := starHermitianInverse q s t htc
  left_inv := starHermitianInverse_left q s t ht htc
  right_inv := starHermitianInverse_right q s t ht htc
  map_add' x y := map_add (starHermitianHom q s t ht htc) x y

end SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
