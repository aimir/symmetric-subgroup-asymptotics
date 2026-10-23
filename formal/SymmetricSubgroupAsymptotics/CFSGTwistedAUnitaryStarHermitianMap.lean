import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryStarGroup
import SymmetricSubgroupAsymptotics.CFSGHermitianTwoByTwoParameters

/-! Normalized Hermitian coordinates for the literal unitary root star.
A genuine nonzero central parameter t removes the signed skew factor.
The actual coefficient B is multiplied on the right by diag(1,-1)
and divided by t. No Hermitian-form identification is assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
open CFSGTwistedAUnitaryNaturalRadical CFSGSerreOrdinaryTwists
open CFSGTwistedANaturalMatrices

theorem star_central_div_fixed (q : CFSG.PrimePower) (s : ℕ)
    (t : q.Extension 2) (ht : t ≠ 0) (htc : t ∈ centralParameters q (s + 1))
    (b : centralParameters q (s + 1)) :
    definingFieldAutomorphism q 2 (b.val / t) = b.val / t := by
  have h := centralParameter_div_fixed q (s + 1) t ht htc b
  change definingFieldAutomorphism q 2 (t⁻¹ * b.val) = t⁻¹ * b.val at h
  simpa only [div_eq_mul_inv, mul_comm] using h

theorem star_offDiagonal_div_sigma (q : CFSG.PrimePower) (s : ℕ)
    (t : q.Extension 2) (htc : t ∈ centralParameters q (s + 1)) (d : q.Extension 2) :
    definingFieldAutomorphism q 2 (d / t) =
      -(parity q (s + 1) * definingFieldAutomorphism q 2 d) / t := by
  rw [map_div₀, centralParameter_sigma q (s + 1) t htc]
  rcases neg_one_pow_eq_or (q.Extension 2) (s + 1) with he | he
  · have he' : parity q (s + 1) = 1 := he
    simp only [he', one_mul, div_neg, neg_div]
  · have he' : parity q (s + 1) = -1 := he
    simp only [he', neg_one_mul, neg_neg]

def starHermitianRaw (q : CFSG.PrimePower) (s : ℕ) (t : q.Extension 2)
    (x : StarParameters q s) : Matrix (Fin 2) (Fin 2) (q.Extension 2) :=
  fun i j => (starCoefficient q s x i j / t) * (if j = 0 then 1 else -1)

theorem starHermitianRaw_zero (q : CFSG.PrimePower) (s : ℕ) (t : q.Extension 2) :
    starHermitianRaw q s t 0 = 0 := by
  ext i j
  change (starCoefficient q s 0 i j / t) * _ = 0
  rw [starCoefficient_zero]
  simp only [Matrix.zero_apply, zero_div, zero_mul]

theorem starHermitianRaw_add (q : CFSG.PrimePower) (s : ℕ) (t : q.Extension 2)
    (x y : StarParameters q s) :
    starHermitianRaw q s t (x + y) = starHermitianRaw q s t x + starHermitianRaw q s t y := by
  ext i j
  have he := congrArg (fun M : Matrix (Fin 2) (Fin 2) (q.Extension 2) => M i j)
    (starCoefficient_add q s x y)
  change starCoefficient q s (x + y) i j = starCoefficient q s x i j + starCoefficient q s y i j at he
  change (starCoefficient q s (x + y) i j / t) * _ =
    (starCoefficient q s x i j / t) * _ + (starCoefficient q s y i j / t) * _
  rw [he, add_div, add_mul]

theorem starHermitianRaw_hermitian (q : CFSG.PrimePower) (s : ℕ)
    (t : q.Extension 2) (ht : t ≠ 0) (htc : t ∈ centralParameters q (s + 1))
    (x : StarParameters q s) :
    CFSGHermitianTwoByTwoRankOne.Hermitian (definingFieldAutomorphism q 2)
      (starHermitianRaw q s t x) := by
  have h00 : definingFieldAutomorphism q 2 (starHermitianRaw q s t x 0 0) =
      starHermitianRaw q s t x 0 0 := by
    change definingFieldAutomorphism q 2 ((x.1.val / t) * 1) = (x.1.val / t) * 1
    simpa only [mul_one] using star_central_div_fixed q s t ht htc x.1
  have h11 : definingFieldAutomorphism q 2 (starHermitianRaw q s t x 1 1) =
      starHermitianRaw q s t x 1 1 := by
    change definingFieldAutomorphism q 2 ((x.2.2.val / t) * (-1)) = (x.2.2.val / t) * (-1)
    rw [map_mul, star_central_div_fixed q s t ht htc x.2.2, map_neg, map_one]
  have h01 : definingFieldAutomorphism q 2 (starHermitianRaw q s t x 1 0) =
      starHermitianRaw q s t x 0 1 := by
    change definingFieldAutomorphism q 2 ((x.2.1 / t) * 1) =
      ((parity q (s + 1) * definingFieldAutomorphism q 2 x.2.1) / t) * (-1)
    rw [mul_one, star_offDiagonal_div_sigma q s t htc x.2.1]
    ring
  have h10 : definingFieldAutomorphism q 2 (starHermitianRaw q s t x 0 1) =
      starHermitianRaw q s t x 1 0 := by
    have h := congrArg (definingFieldAutomorphism q 2) h01
    have hi : definingFieldAutomorphism q 2 (definingFieldAutomorphism q 2
        (starHermitianRaw q s t x 1 0)) = starHermitianRaw q s t x 1 0 :=
      extension_two_pow_twice q _
    rw [hi] at h
    exact h.symm
  intro i j
  fin_cases i <;> fin_cases j
  · exact h00
  · exact h01
  · exact h10
  · exact h11

def starHermitianHom (q : CFSG.PrimePower) (s : ℕ)
    (t : q.Extension 2) (ht : t ≠ 0) (htc : t ∈ centralParameters q (s + 1)) :
    StarParameters q s →+
      CFSGHermitianTwoByTwoRankOne.parameters (definingFieldAutomorphism q 2) where
  toFun x := ⟨starHermitianRaw q s t x, starHermitianRaw_hermitian q s t ht htc x⟩
  map_zero' := Subtype.ext (starHermitianRaw_zero q s t)
  map_add' x y := Subtype.ext (starHermitianRaw_add q s t x y)

theorem starHermitianHom_injective (q : CFSG.PrimePower) (s : ℕ)
    (t : q.Extension 2) (ht : t ≠ 0) (htc : t ∈ centralParameters q (s + 1)) :
    Function.Injective (starHermitianHom q s t ht htc) := by
  intro x y h
  apply starCoefficient_injective q s
  have hh := congrArg
    (fun A : CFSGHermitianTwoByTwoRankOne.parameters (definingFieldAutomorphism q 2) => A.val) h
  ext i j
  have he := congrArg (fun M : Matrix (Fin 2) (Fin 2) (q.Extension 2) => M i j) hh
  change (starCoefficient q s x i j / t) * (if j = 0 then 1 else -1) =
    (starCoefficient q s y i j / t) * (if j = 0 then 1 else -1) at he
  have hw : (if j = 0 then (1 : q.Extension 2) else -1) ≠ 0 := by
    split_ifs <;> simp
  have hd := mul_right_cancel₀ hw he
  have hc := congrArg (fun a : q.Extension 2 => a * t) hd
  simpa only [div_mul_cancel₀ _ ht] using hc

end SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
