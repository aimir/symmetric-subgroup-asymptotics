import SymmetricSubgroupAsymptotics.ProductQuartetOddSubgroup
import SymmetricSubgroupAsymptotics.QuartetOddKernelOrbitCover

/-! The actual odd subgroup has at most eight original point orbits.
Reindexing the four plane points changes neither the original group nor
its action. Correlated local odd images are retained. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.ProductBlockFrame
open BinaryPlanePermutationAffineEquiv
open BinaryPlaneWreathActualOddKernel

variable {X : Type} [Finite X] {T : Subgroup (Equiv.Perm X)}
  (C : ProductBlockFrame T (Fin 4) Plane)

private def planeLabels : Fin 4 ≃ Plane :=
  (Finite.equivFinOfCardEq (by simp [Plane, Nat.card_eq_fintype_card])).symm

private def fourPointFrame : ProductBlockFrame T (Fin 4) (Fin 4) where
  frame := (Equiv.prodCongr (Equiv.refl (Fin 4)) planeLabels).trans C.frame
  top := C.top
  intertwine u p := by
    simpa only [Equiv.trans_apply, Equiv.symm_trans_apply,
      Equiv.prodCongr_apply, Equiv.prodCongr_symm, Equiv.refl_apply]
      using C.intertwine u (p.1,planeLabels p.2)

omit [Finite X] in
private theorem fourPoint_local (i : Fin 4) (u : C.top.ker) (b : Fin 4) :
    (fourPointFrame C).kernelCoordinate i u b =
      planeLabels.symm (C.kernelCoordinate i u (planeLabels b)) := rfl

 theorem odd_subgroup_orbit_card_le
    (P : Subgroup T) (hfix : P≤C.top.ker)
    (hcubic : ∀ p : P,p^3=1)
    (hlocal : ∀ i : Fin 4,∃ p : P,
      C.kernelCoordinate i ⟨p.val,hfix p.property⟩≠1) :
    Nat.card (MulAction.orbitRel.Quotient P X)≤8 := by
  apply QuartetOddKernelOrbitCover.orbit_card_le_eight (fourPointFrame C) P hfix hcubic
  intro i
  obtain ⟨p,hp⟩ := hlocal i
  refine ⟨p,?_⟩
  intro h
  apply hp
  apply Equiv.ext
  intro v
  have hv := congrArg (fun q : Equiv.Perm (Fin 4) => q (planeLabels.symm v)) h
  change (fourPointFrame C).kernelCoordinate i
    ⟨p.val,hfix p.property⟩ (planeLabels.symm v) = planeLabels.symm v at hv
  rw [fourPoint_local, Equiv.apply_symm_apply] at hv
  exact planeLabels.symm.injective hv

 theorem exists_odd_subgroup_eight_orbits [MulAction.IsPretransitive T X]
    (hO : oddKernel C.quartetLinearImage≠⊥) :
    ∃ P : Subgroup T,IsPGroup 3 P ∧
      Nat.card (MulAction.orbitRel.Quotient P X)≤8 := by
  obtain ⟨P,hfix,hP,hcubic,hlocal⟩ := C.exists_quartet_odd_subgroup hO
  exact ⟨P,hP,C.odd_subgroup_orbit_card_le P hfix hcubic hlocal⟩

end SymmetricSubgroupAsymptotics.ProductBlockFrame
