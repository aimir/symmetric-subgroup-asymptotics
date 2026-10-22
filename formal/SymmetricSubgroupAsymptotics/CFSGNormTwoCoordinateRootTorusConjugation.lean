import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckDiagonalTorus
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateRootHeightLeading
import SymmetricSubgroupAsymptotics.CFSGWeightedDiagonalConjugation
import SymmetricSubgroupAsymptotics.CFSGGradedQuadraticUnit

/-! Actual simple torus conjugation on EVERY original selected root
element. Original integer lattice support supplies the character before
base change; no field-valued weight separation is used. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateRootTorusConjugation
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing
open CFSGNormTwoGeckLatticeDegree CFSGNormTwoGeckDiagonalTorus
open CFSGNormTwoGeckParameterizedTorus CFSGNormTwoCoordinateRootHeightLeading
open CFSGNormTwoCoordinateRootBracketTransport CFSGNormTwoCoordinateRootCoefficientCoordinates
open CFSGNormTwoCoordinateSelectedRootElement CFSGGradedMatrixSupport
variable {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ) (hd : ∀i,A i i=2)
    (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    (ho : ∀i j,i≠j→A i j≤0)
    [Fintype (Roots A)] [DecidableEq (Roots A)]
    [(rootPairing A hs hp).IsReduced] [(rootPairing A hs hp).IsIrreducible]
local notation "b₀" => coordinateBase A hd hs hp ho
local notation "s₀" => coordinateIndexEquiv A hd hs hp ho
local notation "ell" => latticeWeight A hs hp b₀
private abbrev CoordMat (K : Type) := Matrix ((b₀).support⊕Roots A) ((b₀).support⊕Roots A) K

theorem torus_mul_selected_root (K : Type) [Field K] (i : Fin r) (t : Kˣ)
    (k : Roots A) (a : K) :
    parameterTorus A hs hp b₀ s₀ K i t*selectedRootElement A hd hs hp ho K k a=
      selectedRootElement A hd hs hp ho K k
        (a*(t:K)^(integerPairing A (s₀ i : Roots A).val k.val))*
      parameterTorus A hs hp b₀ s₀ K i t := by
  let f : (Fin r→ℤ)→ₗ[ℤ]ℤ := integerPairing A (s₀ i : Roots A).val
  have hw : weight A hs hp b₀ s₀ i=(fun j=>f (ell j)) := by
    funext j
    rcases j with j|j
    · simp only [weight,latticeWeight,map_zero]
    · rfl
  have hX := CFSGGradedQuadraticUnit.support_apply_height ell k.val f.toAddMonoidHom
    (selectedFieldCoefficient A hd hs hp ho K k)
    (selectedFieldCoefficient_support A hd hs hp ho K k)
  have hY := CFSGGradedQuadraticUnit.support_apply_height ell (k.val+k.val) f.toAddMonoidHom
    (selectedSecondCoefficient A hd hs hp ho K k)
    (selectedSecondCoefficient_support A hd hs hp ho K k)
  have hX' : Supported (weight A hs hp b₀ s₀ i)
      (fun w=>w+integerPairing A (s₀ i : Roots A).val k.val)
      (selectedFieldCoefficient A hd hs hp ho K k) := by
    rw [hw]
    exact hX
  have hY' : Supported (weight A hs hp b₀ s₀ i)
      (fun w=>w+2*integerPairing A (s₀ i : Roots A).val k.val)
      (selectedSecondCoefficient A hd hs hp ho K k) := by
    rw [hw]
    simpa only [map_add,two_mul] using hY
  apply Units.ext
  change (parameterTorus A hs hp b₀ s₀ K i t : CoordMat A hd hs hp ho K)*
      (selectedRootElement A hd hs hp ho K k a : CoordMat A hd hs hp ho K)=
    (selectedRootElement A hd hs hp ho K k
      (a*(t:K)^(integerPairing A (s₀ i : Roots A).val k.val)) : CoordMat A hd hs hp ho K)*
      (parameterTorus A hs hp b₀ s₀ K i t : CoordMat A hd hs hp ho K)
  rw [torus_diagonal,selectedRootElement_expansion,selectedRootElement_expansion]
  exact CFSGWeightedDiagonalConjugation.quadratic_mul_scaled (weight A hs hp b₀ s₀ i) t
    (integerPairing A (s₀ i : Roots A).val k.val)
    (selectedFieldCoefficient A hd hs hp ho K k) (selectedSecondCoefficient A hd hs hp ho K k) hX' hY' a

theorem torus_conjugate_selected_root (K : Type) [Field K] (i : Fin r) (t : Kˣ)
    (k : Roots A) (a : K) :
    parameterTorus A hs hp b₀ s₀ K i t*selectedRootElement A hd hs hp ho K k a*
        (parameterTorus A hs hp b₀ s₀ K i t)⁻¹=
      selectedRootElement A hd hs hp ho K k
        (a*(t:K)^(integerPairing A (s₀ i : Roots A).val k.val)) := by
  rw [torus_mul_selected_root,mul_assoc,mul_inv_cancel,mul_one]

end SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateRootTorusConjugation
