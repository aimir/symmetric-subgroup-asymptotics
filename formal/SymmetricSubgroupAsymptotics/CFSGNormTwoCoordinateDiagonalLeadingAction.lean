import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateLeadingHom
import SymmetricSubgroupAsymptotics.CFSGDiagonalMatrixUnits

/-! Diagonal conjugation on the actual simple leading coordinates.
Its scalar is determined by the action on the same simple root at one. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateDiagonalLeadingAction
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing CFSGSerreQuadraticMatrix
open CFSGNormTwoGeckIntegralRealization CFSGNormTwoGeckColumns
open CFSGNormTwoGeckPositivePGroup CFSGNormTwoCoordinateLeadingFactor
open CFSGNormTwoCoordinateLeadingHom CFSGDiagonalMatrixUnits
variable {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ) (hd : ∀i,A i i=2)
    (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    (ho : ∀i j,i≠j→A i j≤0)
    [Fintype (Roots A)] [DecidableEq (Roots A)] [(rootPairing A hs hp).IsIrreducible]
local notation "b₀" => coordinateBase A hd hs hp ho
local notation "s₀" => coordinateIndexEquiv A hd hs hp ho
local notation "D" => realizationData A hs hp b₀ s₀

omit [(rootPairing A hs hp).IsIrreducible] in
theorem diagonal_conjugate_leading (K : Type) [Field K] (d : (b₀).support⊕Roots A→Kˣ)
    (u : (Matrix ((b₀).support⊕Roots A) ((b₀).support⊕Roots A) K)ˣ) (i : Fin r) :
    leadingCoordinates A hd hs hp ho K (diagonalHom ((b₀).support⊕Roots A) K d*u*(diagonalHom ((b₀).support⊕Roots A) K d)⁻¹) i=
      (d (Sum.inl (s₀ i)) : K)*leadingCoordinates A hd hs hp ho K u i*
        ((d (Sum.inr (negativeIndex A hs hp (s₀ i))))⁻¹ : Kˣ) := by
  rw [←map_inv]
  change (((diagonalHom ((b₀).support⊕Roots A) K d : Matrix ((b₀).support⊕Roots A) ((b₀).support⊕Roots A) K)*(u : Matrix ((b₀).support⊕Roots A) ((b₀).support⊕Roots A) K))*
    (diagonalHom ((b₀).support⊕Roots A) K (d⁻¹) : Matrix ((b₀).support⊕Roots A) ((b₀).support⊕Roots A) K))
      (Sum.inl (s₀ i)) (Sum.inr (negativeIndex A hs hp (s₀ i)))=_
  simp only [diagonalHom_val,Matrix.mul_diagonal,Matrix.diagonal_mul]
  rfl

private theorem simple_leading_self (K : Type) [Field K] (i : Fin r) (a : K) :
    leadingCoordinates A hd hs hp ho K (canonicalRoot D K false i a) i=a := by
  have h := congrArg (fun z : Multiplicative (Fin r→K)=>z.toAdd i)
    (leadingHom_positiveRoot A hd hs hp ho K i a)
  change leadingCoordinates A hd hs hp ho K (canonicalRoot D K false i a) i=
    (Pi.single i a : Fin r→K) i at h
  simpa only [Pi.single_eq_same] using h

theorem diagonal_leading_of_simple_action (K : Type) [Field K] (d : (b₀).support⊕Roots A→Kˣ)
    (u : (Matrix ((b₀).support⊕Roots A) ((b₀).support⊕Roots A) K)ˣ) (i : Fin r) (c : K)
    (hact : diagonalHom ((b₀).support⊕Roots A) K d*canonicalRoot D K false i 1*(diagonalHom ((b₀).support⊕Roots A) K d)⁻¹=
      canonicalRoot D K false i c) :
    leadingCoordinates A hd hs hp ho K (diagonalHom ((b₀).support⊕Roots A) K d*u*(diagonalHom ((b₀).support⊕Roots A) K d)⁻¹) i=
      c*leadingCoordinates A hd hs hp ho K u i := by
  have hc := congrArg (fun z : (Matrix ((b₀).support⊕Roots A) ((b₀).support⊕Roots A) K)ˣ=>leadingCoordinates A hd hs hp ho K z i) hact
  dsimp only at hc
  rw [diagonal_conjugate_leading,simple_leading_self,simple_leading_self,mul_one] at hc
  rw [diagonal_conjugate_leading,←hc]
  ring

end SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateDiagonalLeadingAction
