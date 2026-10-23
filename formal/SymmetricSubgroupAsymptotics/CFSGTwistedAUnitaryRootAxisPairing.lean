import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryProjectiveJointFixed
import SymmetricSubgroupAsymptotics.CFSGHermitianOrthogonality

/-! The covector of an actual conjugate central root is exactly its
signed-Hermitian pairing covector. Reciprocal zero pairing and isotropy
are retained in every characteristic, with the original signed form. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix

namespace SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
open CFSGTwistedANaturalMatrices CFSGTwistedAUpperUnipotent
open CFSGTwistedAUnitaryParameters CFSGSerreOrdinaryTwists

def unitaryNaturalPair (q : CFSG.PrimePower) (r : ℕ)
    (v w : Fin (r + 1) → q.Extension 2) : q.Extension 2 :=
  hermitianPair (definingFieldAutomorphism q 2)
    (signedReversalUnit (q.Extension 2) r : Mat (q.Extension 2) r) v w

theorem unitaryNaturalPair_first (q : CFSG.PrimePower) (r : ℕ)
    (x : Fin (r + 1) → q.Extension 2) :
    unitaryNaturalPair q r (Pi.single (0 : Fin (r + 1)) 1) x = x (Fin.last r) := by
  let sigma := definingFieldAutomorphism q 2
  have hs : sigma ∘ (Pi.single (0 : Fin (r + 1)) (1 : q.Extension 2)) = Pi.single 0 1 := by
    funext i
    by_cases hi : i = 0 <;> simp only [Function.comp_apply, Pi.single_apply, hi,
      if_true, if_false, map_one, map_zero]
  have hrow : (signedReversalUnit (q.Extension 2) r : Mat (q.Extension 2) r) 0 =
      Pi.single (Fin.last r) 1 := by
    funext i
    have hr : (0 : Fin (r + 1)).rev = Fin.last r := by apply Fin.ext; simp [Fin.rev]
    simp only [signedReversalUnit_apply, hr, signWeight, Fin.val_zero, pow_zero,
      Pi.single_apply, eq_comm]
  change dotProduct (sigma ∘ Pi.single 0 1)
    ((signedReversalUnit (q.Extension 2) r : Mat (q.Extension 2) r) *ᵥ x) = _
  rw [hs, single_dotProduct, one_mul]
  change dotProduct ((signedReversalUnit (q.Extension 2) r : Mat (q.Extension 2) r) 0) x = _
  rw [hrow, single_dotProduct, one_mul]

def unitaryCentralVector (q : CFSG.PrimePower) (s : ℕ) (g : naturalFixed (s + 3) q) :
    Fin (s + 4) → q.Extension 2 :=
  (g.val.val : Mat (q.Extension 2) (s + 3)) *ᵥ Pi.single (0 : Fin (s + 4)) 1

theorem unitaryCentralVector_pair (q : CFSG.PrimePower) (s : ℕ)
    (g : naturalFixed (s + 3) q) (x : Fin (s + 4) → q.Extension 2) :
    unitaryNaturalPair q (s + 3) (unitaryCentralVector q s g) x =
      centralRootAxisFunctional q s g x := by
  have hh := hermitianPair_isometry (definingFieldAutomorphism q 2)
    (signedReversalUnit (q.Extension 2) (s + 3) : Mat (q.Extension 2) (s + 3))
    (g.val.val : Mat (q.Extension 2) (s + 3)) (naturalFixed_signedForm q (s + 3) g)
    (Pi.single (0 : Fin (s + 4)) 1)
    ((↑(g.val.val⁻¹) : Mat (q.Extension 2) (s + 3)) *ᵥ x)
  rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec] at hh
  change unitaryNaturalPair q (s + 3) (unitaryCentralVector q s g) x =
    unitaryNaturalPair q (s + 3) (Pi.single 0 1)
      ((↑(g.val.val⁻¹) : Mat (q.Extension 2) (s + 3)) *ᵥ x) at hh
  exact hh.trans (unitaryNaturalPair_first q (s + 3) _)

theorem centralRootAxisFunctional_self (q : CFSG.PrimePower) (s : ℕ)
    (g : naturalFixed (s + 3) q) :
    centralRootAxisFunctional q s g (unitaryCentralVector q s g) = 0 := by
  change ((↑(g.val.val⁻¹) : Mat (q.Extension 2) (s + 3)) *ᵥ
    ((g.val.val : Mat (q.Extension 2) (s + 3)) *ᵥ Pi.single (0 : Fin (s + 4)) 1))
      (Fin.last (s + 3)) = 0
  rw [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
  have hn : (Fin.last (s + 3) : Fin (s + 4)) ≠ 0 := by
    intro h
    have hh := congrArg (fun i : Fin (s + 4) => i.val) h
    change s + 3 = 0 at hh
    omega
  simp only [Pi.single_apply, if_neg hn]

theorem centralRootAxisFunctional_ne_zero (q : CFSG.PrimePower) (s : ℕ)
    (g : naturalFixed (s + 3) q) : centralRootAxisFunctional q s g ≠ 0 := by
  intro hf
  have hh := congrArg (fun f : Module.Dual (q.Extension 2) (Fin (s + 4) → q.Extension 2) =>
    f ((g.val.val : Mat (q.Extension 2) (s + 3)) *ᵥ Pi.single (Fin.last (s + 3)) 1)) hf
  change ((↑(g.val.val⁻¹) : Mat (q.Extension 2) (s + 3)) *ᵥ
    ((g.val.val : Mat (q.Extension 2) (s + 3)) *ᵥ Pi.single (Fin.last (s + 3)) 1))
      (Fin.last (s + 3)) = 0 at hh
  rw [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec, Pi.single_eq_same] at hh
  exact one_ne_zero hh

theorem unitaryNaturalPair_zero_swap (q : CFSG.PrimePower) (r : ℕ)
    (v w : Fin (r + 1) → q.Extension 2) :
    unitaryNaturalPair q r v w = 0 ↔ unitaryNaturalPair q r w v = 0 := by
  apply CFSGHermitianOrthogonality.zero_iff_swap_of_transpose
    (definingFieldAutomorphism q 2) (fun a => extension_two_pow_twice q a)
    ((-1 : q.Extension 2) ^ r) (pow_ne_zero r (neg_ne_zero.mpr one_ne_zero))
    (signedReversalUnit (q.Extension 2) r : Mat (q.Extension 2) r) ?_ v w
  have hm : (signedReversalUnit (q.Extension 2) r : Mat (q.Extension 2) r).map
      (definingFieldAutomorphism q 2) = signedReversalUnit (q.Extension 2) r :=
    map_signedReversalUnit_val (definingFieldAutomorphism q 2).toRingHom r
  rw [hm, signedReversalUnit_transpose]

theorem centralRootAxisFunctional_zero_reciprocal (q : CFSG.PrimePower) (s : ℕ)
    (g h : naturalFixed (s + 3) q) :
    centralRootAxisFunctional q s g (unitaryCentralVector q s h) = 0 ↔
      centralRootAxisFunctional q s h (unitaryCentralVector q s g) = 0 := by
  rw [← unitaryCentralVector_pair, ← unitaryCentralVector_pair]
  exact unitaryNaturalPair_zero_swap q (s + 3) _ _

end SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
