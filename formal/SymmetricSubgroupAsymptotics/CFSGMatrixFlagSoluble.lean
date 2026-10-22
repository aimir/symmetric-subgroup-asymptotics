import SymmetricSubgroupAsymptotics.CFSGMatrixFlagSubgroups
import SymmetricSubgroupAsymptotics.CFSGUpperTriangularSoluble

/-! Solubility of the actual matrix-unit group preserving a specified
complete coordinate flag, transported to the existing triangular proof. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
universe u
namespace SymmetricSubgroupAsymptotics.CFSGMatrixFlagSubgroups
variable {I K : Type u} [Fintype I] [DecidableEq I] [Field K] {m : ℕ}

theorem borelUnits_soluble (e : I≃Fin m) : IsSolvable
    (borelUnits e : Subgroup ((Matrix I I K)ˣ)) := by
  let rho : borelUnits e→*Matrix (Fin m) (Fin m) K :=
    (Matrix.reindexAlgEquiv K K e).toMonoidHom.comp
      ((Units.coeHom _).comp (borelUnits e).subtype)
  apply CFSGUpperUnitriangular.soluble_of_faithful_upper_matrix K m (borelUnits e) rho
  · intro x y h
    apply Subtype.ext
    apply Units.ext
    exact (Matrix.reindexAlgEquiv K K e).injective h
  · intro g i j hij
    change (g.val : Matrix I I K) (e.symm i) (e.symm j)=0
    apply g.property
    simpa only [Equiv.apply_symm_apply] using hij

end SymmetricSubgroupAsymptotics.CFSGMatrixFlagSubgroups
