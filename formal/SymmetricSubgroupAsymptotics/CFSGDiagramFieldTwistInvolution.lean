import SymmetricSubgroupAsymptotics.CFSGSerreQuadraticDiagramFieldTwist
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateDiagramIndices

/-! Literal involution identities for diagram--field matrix twists.
These provide the compatibility of signed paired coordinates from the
actual matrix action, rather than imposing compatibility on root signs. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGDiagramFieldTwistInvolution
open CFSGSerreQuadraticDiagramFieldTwist CFSGNormTwoCoordinateDiagramIndices
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing CFSGNormTwoCartanDiagramRoots

private theorem inverse_twice {I : Type*} (e : Equiv.Perm I)
    (he : Function.Involutive e) (i : I) : e.symm (e.symm i) = i := by
  have hi (j : I) : e.symm j = e j := by
    apply e.injective
    rw [e.apply_symm_apply, he]
  rw [hi, hi, he]

theorem matrixTwist_involutive {I K : Type*} [Fintype I] [DecidableEq I] [CommRing K]
    (e : Equiv.Perm I) (he : Function.Involutive e) (sigma : K ≃+* K)
    (hsigma : Function.Involutive sigma) : Function.Involutive (matrixTwist e K sigma) := by
  intro M
  ext i j
  change sigma (sigma (M (e.symm (e.symm i)) (e.symm (e.symm j)))) = M i j
  rw [inverse_twice e he, inverse_twice e he, hsigma]

theorem unitTwist_involutive {I K : Type*} [Fintype I] [DecidableEq I] [CommRing K]
    (e : Equiv.Perm I) (he : Function.Involutive e) (sigma : K ≃+* K)
    (hsigma : Function.Involutive sigma) : Function.Involutive (unitTwist e K sigma) := by
  intro g
  apply Units.ext
  change matrixTwist e K sigma (matrixTwist e K sigma g.val) = g.val
  exact matrixTwist_involutive e he sigma hsigma g.val

theorem combinedIndex_involutive {I : Type*} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℤ) (hd : ∀ i, A i i = 2) (hs : A.transpose = A)
    (hp : (rationalMatrix A).PosDef) (ho : ∀ i j, i ≠ j → A i j ≤ 0)
    [Fintype (Roots A)] [DecidableEq (Roots A)]
    (p : Equiv.Perm I) (hA : ∀ i j, A (p i) (p j) = A i j)
    (hpinv : Function.Involutive p) :
    Function.Involutive (combinedIndex A hd hs hp ho p hA) := by
  intro z
  cases z with
  | inl i =>
    apply congrArg Sum.inl
    change (coordinateIndexEquiv A hd hs hp ho)
      (p ((coordinateIndexEquiv A hd hs hp ho).symm
        ((coordinateIndexEquiv A hd hs hp ho)
          (p ((coordinateIndexEquiv A hd hs hp ho).symm i))))) = i
    rw [Equiv.symm_apply_apply, hpinv, Equiv.apply_symm_apply]
  | inr k =>
    apply congrArg Sum.inr
    apply Subtype.ext
    funext j
    change k.val (p.symm (p.symm j)) = k.val j
    rw [inverse_twice p hpinv]

end SymmetricSubgroupAsymptotics.CFSGDiagramFieldTwistInvolution
