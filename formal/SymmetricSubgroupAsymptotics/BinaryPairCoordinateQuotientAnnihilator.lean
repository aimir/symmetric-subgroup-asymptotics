import SymmetricSubgroupAsymptotics.BinaryPairAxisNaturalModule
import SymmetricSubgroupAsymptotics.BinaryPairOriginalCoordinateRepresentation
import SymmetricSubgroupAsymptotics.BinaryPairOriginalKernelCoordinateCard

/-! Original-coordinate displacement annihilators descend to the SAME
actual outer affine quotient module. Only reversible linear transport is
used; no quotient module, original kernel, or offset class is replaced. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryPairFrame
variable {X : Type} [Finite X] {U : Subgroup (Equiv.Perm X)}
    (F : BinaryPairFrame U (Fin 16)) (E : BinaryPairFrame F.top.range (Fin 8))
include F E

omit [Finite X] in
private theorem coordinate_displacement (t : F.top.range) (v : Fin 16 → ZMod 2) :
    E.originalCoordinateRepresentation t (E.originalCoordinateEquiv v)-E.originalCoordinateEquiv v=
      E.originalCoordinateEquiv (F.coordinateTopAction t v-v) := by
  change E.originalCoordinateEquiv
      (F.coordinateTopAction t (E.originalCoordinateEquiv.symm (E.originalCoordinateEquiv v)))-
    E.originalCoordinateEquiv v=E.originalCoordinateEquiv _
  rw [E.originalCoordinateEquiv.symm_apply_apply,map_sub]

private theorem kernel_space_map {d : ℕ} (K : BinaryCoordinateSpace 16 d)
    (hS : (E.originalCoordinateSubrepresentation (F.axisNaturalSubrepresentation F.top.ker)).toSubmodule=K.space) :
    F.kernelSpace.map E.originalCoordinateEquiv.toLinearMap=K.space := by
  change (F.ambientAxis F.top.ker).map E.originalCoordinateEquiv.toLinearMap=_ at hS
  simpa only [F.original_ambientAxis_kernel] using hS

private theorem original_mem_of_coordinate_mem {d : ℕ} (K : BinaryCoordinateSpace 16 d)
    (hS : (E.originalCoordinateSubrepresentation (F.axisNaturalSubrepresentation F.top.ker)).toSubmodule=K.space)
    (v : Fin 16 → ZMod 2) (hv : E.originalCoordinateEquiv v∈K.space) : v∈F.kernelSpace := by
  rw [←kernel_space_map F E K hS] at hv
  obtain ⟨a,ha,he⟩ := hv
  have he' : a=v := E.originalCoordinateEquiv.injective he
  exact he' ▸ ha

theorem affineQuotient_eq_one_of_original_coordinate_displacement {d : ℕ}
    (K : BinaryCoordinateSpace 16 d)
    (hS : (E.originalCoordinateSubrepresentation (F.axisNaturalSubrepresentation F.top.ker)).toSubmodule=K.space)
    (j : F.top.range)
    (hj : ∀ v : Fin 16 → ZMod 2,E.originalCoordinateRepresentation j v-v∈K.space) :
    F.affineQuotientRepresentation j=1 := by
  apply LinearMap.ext
  intro a
  obtain ⟨v,rfl⟩ := F.kernelSpace.mkQ_surjective a
  change F.kernelSpace.mkQ (F.coordinateTopAction j v)=F.kernelSpace.mkQ v
  apply (Submodule.Quotient.eq F.kernelSpace).mpr
  apply original_mem_of_coordinate_mem F E K hS
  have hh := hj (E.originalCoordinateEquiv v)
  rwa [coordinate_displacement F E j v] at hh

theorem affineQuotient_double_annihilator_of_original_coordinate {d : ℕ}
    (K : BinaryCoordinateSpace 16 d)
    (hS : (E.originalCoordinateSubrepresentation (F.axisNaturalSubrepresentation F.top.ker)).toSubmodule=K.space)
    (g h : F.top.range)
    (hAnn : ∀ v : Fin 16 → ZMod 2,
      E.originalCoordinateRepresentation g (E.originalCoordinateRepresentation h v-v)-
        (E.originalCoordinateRepresentation h v-v)∈K.space) :
    ∀ v : (Fin 16 → ZMod 2) ⧸ F.kernelSpace,
      F.affineQuotientRepresentation g (F.affineQuotientRepresentation h v-v)-
        (F.affineQuotientRepresentation h v-v)=0 := by
  intro a
  obtain ⟨v,rfl⟩ := F.kernelSpace.mkQ_surjective a
  have hsub : F.affineQuotientRepresentation h (F.kernelSpace.mkQ v)-F.kernelSpace.mkQ v=
      F.kernelSpace.mkQ (F.coordinateTopAction h v-v) := by
    change F.kernelSpace.mkQ (F.coordinateTopAction h v)-F.kernelSpace.mkQ v=_
    rw [map_sub]
  rw [hsub]
  change F.kernelSpace.mkQ (F.coordinateTopAction g (F.coordinateTopAction h v-v))-
    F.kernelSpace.mkQ (F.coordinateTopAction h v-v)=0
  rw [←map_sub]
  apply (Submodule.Quotient.mk_eq_zero F.kernelSpace).mpr
  apply original_mem_of_coordinate_mem F E K hS
  have hh := hAnn (E.originalCoordinateEquiv v)
  rwa [coordinate_displacement F E h v,
    coordinate_displacement F E g (F.coordinateTopAction h v-v)] at hh
end SymmetricSubgroupAsymptotics.BinaryPairFrame
