import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckLatticeDegree
import SymmetricSubgroupAsymptotics.CFSGNormTwoPairingBounds

/-! The literal Cartan/root coordinate weights of the norm-two Geck
module have squared diameter at most eight. Consequently an ambient
matrix supported in a degree of larger norm is zero. This is only a
support statement; it makes no assertion about generated root spaces. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoGeckWeightDiameter
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing CFSGNormTwoPairingBounds
open CFSGNormTwoGeckLatticeDegree CFSGGradedMatrixSupport
variable {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℤ) (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    [Fintype (Roots A)] [DecidableEq (Roots A)]
    (b : (rootPairing A hs hp).Base)

omit [Fintype (Roots A)] [DecidableEq (Roots A)] in
theorem weight_difference_norm_le_eight (x y : b.support⊕Roots A) :
    integerPairing A (latticeWeight A hs hp b x-latticeWeight A hs hp b y)
      (latticeWeight A hs hp b x-latticeWeight A hs hp b y)≤8 := by
  cases x with
  | inl i=>
    cases y with
    | inl j=>
      change integerPairing A (0-0) (0-0)≤8
      simp
    | inr k=>
      change integerPairing A (0-k.val) (0-k.val)≤8
      simp only [zero_sub,map_neg,LinearMap.neg_apply,neg_neg,k.property]
      norm_num
  | inr k=>
    cases y with
    | inl j=>
      change integerPairing A (k.val-0) (k.val-0)≤8
      simp only [sub_zero,k.property]
      norm_num
    | inr l=>
      change integerPairing A (k.val-l.val) (k.val-l.val)≤8
      rw [norm_sub A hs,k.property,l.property]
      have hkl := (root_pairing_bounds A hs hp k l).1
      omega

theorem supported_eq_zero_of_norm_gt_eight {K : Type*} [Semiring K]
    (d : n→ℤ) (hd : 8 < integerPairing A d d)
    (M : Matrix (b.support⊕Roots A) (b.support⊕Roots A) K)
    (hM : Supported (latticeWeight A hs hp b) (fun v=>v+d) M) : M=0 := by
  apply Matrix.ext
  intro x y
  apply hM x y
  intro he
  dsimp only at he
  have hxy := weight_difference_norm_le_eight A hs hp b x y
  have hdiff : latticeWeight A hs hp b x-latticeWeight A hs hp b y=d := by
    rw [he]
    exact add_sub_cancel_left _ _
  rw [hdiff] at hxy
  omega

end SymmetricSubgroupAsymptotics.CFSGNormTwoGeckWeightDiameter
