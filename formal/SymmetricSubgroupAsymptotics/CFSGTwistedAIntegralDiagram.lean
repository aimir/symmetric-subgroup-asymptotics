import SymmetricSubgroupAsymptotics.CFSGTwistedARationalDiagram
import SymmetricSubgroupAsymptotics.CFSGTwistedANaturalDiagramScalars

/-! The actual integral-lattice and tensor-base-change diagram action
intertwines with the signed anti-diagonal map on the same natural matrix
image, in every characteristic. No replacement lattice is introduced. -/

set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped TensorProduct

namespace SymmetricSubgroupAsymptotics.CFSGTwistedANaturalMatrices
open CFSG.Models.Chevalley

theorem integralNatural_diagram (r : ℕ) (x : integralLattice (CartanMatrix.A r)) :
    CFSGSerreSquareZeroMatrix.integralRepresentation (realizationData r)
      (CFSGSerreDiagram.integralEquiv (CartanMatrix.A r) Fin.revPerm
        (CFSGSerreDiagram.typeA_reverse_preserves r) x) =
      matrixDiagram ℤ r (CFSGSerreSquareZeroMatrix.integralRepresentation (realizationData r) x) := by
  apply CFSGSerreSquareZeroMatrix.integerCast_injective (Fin (r + 1))
  calc
    _ = rationalNatural r
        (CFSGSerreDiagram.integralEquiv (CartanMatrix.A r) Fin.revPerm
          (CFSGSerreDiagram.typeA_reverse_preserves r) x).val :=
      CFSGSerreSquareZeroMatrix.integralRepresentation_cast (realizationData r) _
    _ = matrixDiagram ℚ r (rationalNatural r x.val) := by
      simpa only [CFSGSerreDiagram.integralEquiv_coe_apply] using
        rationalNatural_diagramEquiv r x.val
    _ = matrixDiagram ℚ r
        (CFSGSerreSquareZeroMatrix.integerCast (Fin (r + 1))
          (CFSGSerreSquareZeroMatrix.integralRepresentation (realizationData r) x)) :=
      congrArg (matrixDiagram ℚ r)
        (CFSGSerreSquareZeroMatrix.integralRepresentation_cast (realizationData r) x).symm
    _ = _ :=
      (map_matrixDiagram (Int.castRingHom ℚ) r
        (CFSGSerreSquareZeroMatrix.integralRepresentation (realizationData r) x)).symm

theorem naturalBaseChange_diagram (K : Type) [Field K] (r : ℕ)
    (x : Space (CartanMatrix.A r) K) :
    CFSGSerreSquareZeroMatrix.baseChange (realizationData r) K
      (CFSGSerreDiagram.spaceEquiv (CartanMatrix.A r) K Fin.revPerm
        (CFSGSerreDiagram.typeA_reverse_preserves r) x) =
      matrixDiagram K r (CFSGSerreSquareZeroMatrix.baseChange (realizationData r) K x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul a x =>
    simp only [CFSGSerreDiagram.spaceEquiv, LinearEquiv.baseChange_tmul,
      CFSGSerreSquareZeroMatrix.baseChange_tmul]
    rw [integralNatural_diagram, map_matrixDiagram, map_smul]
  | add x y hx hy => simp only [map_add, hx, hy]

end SymmetricSubgroupAsymptotics.CFSGTwistedANaturalMatrices
