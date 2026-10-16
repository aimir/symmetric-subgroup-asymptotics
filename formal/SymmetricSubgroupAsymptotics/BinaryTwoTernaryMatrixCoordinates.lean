import SymmetricSubgroupAsymptotics.BinaryTwoTernaryMatrixBlocks

/-! Coordinate-independent interface for the checked two-ternary matrix
operators. A different original action may use a different reversible
sparse chart while sharing the same matrix/PID proof and fibre witnesses. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical MonoidAlgebra Polynomial

namespace SymmetricSubgroupAsymptotics.BinaryTwoTernaryMatrixBlocks

variable {G : Type} [Group G]

theorem uniform_of_coordinates (coords : Vector ≃ₗ[ZMod 2] Blocks) (rho : Representation (ZMod 2) G Vector) (c d s : G)
    (hmatrix : ∀ (i : Fin 2) (r t : Fin (rowCount i)) (q : Fin 12)
      (j : Fin 2) (u : Fin (rowCount j)) (z : Fin (dimension j)),
      coords (matrixUnitOperator rho c d s i r t (Pi.single q 1)) j u z =
        (Pi.single i (Pi.single r (coords (Pi.single q 1) i t)) : Blocks) j u z)
    (hoperator : ∀ (i : Fin 2) (r : Fin (rowCount i)) (q : Fin 12) (z : Fin (dimension i)),
      coords (actualOperator rho c d s i (Pi.single q 1)) i r z =
        fibreOperator i (coords (Pi.single q 1) i r) z) :
    UniformSubrepresentationGeneratorBound rho 1 := by
  apply (uniformSubrepresentationGeneratorBound_iff_submodule rho 1).mpr
  intro W
  let e := rho.asModuleEquiv.trans coords
  refine ModuleGeneratedBy.one_of_polynomial_matrix_blocks rowCount Fibre e
    (matrixUnitScalar c d s) (operatorScalar c d s) fibreOperator ?_ ?_
    (fun i r ↦ Module.AEval'.of (fibreOperator i) ((fibreWitness i).vectors r 0)) ?_ W
  · intro i r t x
    change coords (rho.asAlgebraHom (matrixUnitScalar c d s i r t) x) =
      Pi.single i (Pi.single r (coords x i t))
    rw [← matrixUnitOperator_eq]
    have h : coords.toLinearMap.comp (matrixUnitOperator rho c d s i r t) =
        ((LinearMap.single (ZMod 2) (fun j ↦ Fin (rowCount j) → Fibre j) i).comp
          ((LinearMap.single (ZMod 2) (fun _ : Fin (rowCount i) ↦ Fibre i) r).comp
            ((LinearMap.proj t : (Fin (rowCount i) → Fibre i) →ₗ[ZMod 2] Fibre i).comp
              (LinearMap.proj i : Blocks →ₗ[ZMod 2] (Fin (rowCount i) → Fibre i))))).comp
          coords.toLinearMap := by
      apply (Pi.basisFun (ZMod 2) (Fin 12)).ext
      intro q
      rw [Pi.basisFun_apply]
      funext j u z
      exact hmatrix i r t q j u z
    exact LinearMap.congr_fun h x
  · intro i r x
    change coords (rho.asAlgebraHom (operatorScalar c d s i) x) i r =
      fibreOperator i (coords x i r)
    rw [← actualOperator_eq]
    have h : (LinearMap.proj r : (Fin (rowCount i) → Fibre i) →ₗ[ZMod 2] Fibre i).comp
        ((LinearMap.proj i : Blocks →ₗ[ZMod 2] (Fin (rowCount i) → Fibre i)).comp
          (coords.toLinearMap.comp (actualOperator rho c d s i))) =
        (fibreOperator i).comp
          ((LinearMap.proj r : (Fin (rowCount i) → Fibre i) →ₗ[ZMod 2] Fibre i).comp
            ((LinearMap.proj i : Blocks →ₗ[ZMod 2] (Fin (rowCount i) → Fibre i)).comp
              coords.toLinearMap)) := by
      apply (Pi.basisFun (ZMod 2) (Fin 12)).ext
      intro q
      rw [Pi.basisFun_apply]
      exact funext (hoperator i r q)
    exact LinearMap.congr_fun h x
  · exact fun i ↦ (fibreWitness i).polynomial_span

end SymmetricSubgroupAsymptotics.BinaryTwoTernaryMatrixBlocks

end
