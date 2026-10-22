import SymmetricSubgroupAsymptotics.CFSGCliffordComponentSpaces
import Mathlib.LinearAlgebra.DFinsupp
import Mathlib.Algebra.BigOperators.Pi

/-! Actual coordinates on the canonical isotypic direct sum. The kernel
of the ambient permutation preserves the zero kernel of every coordinate,
as required by the literal block-order-divisor theorem. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical MonoidAlgebra

namespace SymmetricSubgroupAsymptotics.CFSGCliffordComponentCoordinates
open CFSGCliffordIsotypicTransport CFSGCliffordIsotypicPermutation
  CFSGCliffordComponentSpaces

variable {k G V : Type} [Field k] [Group G] [AddCommGroup V] [Module k V]
  (rho : Representation k G V) (H : Subgroup G) [H.Normal] [Finite V]

omit [H.Normal] in
theorem components_finite : Finite (Components rho H) := by
  letI : Finite (restricted rho H).asModule := Finite.of_injective
    (restricted rho H).asModuleEquiv (restricted rho H).asModuleEquiv.injective
  letI : Finite (Submodule k[H] (restricted rho H).asModule) :=
    Finite.of_injective
      (fun S : Submodule k[H] (restricted rho H).asModule =>
        (S : Set (restricted rho H).asModule)) SetLike.coe_injective
  exact Finite.of_injective (fun C : Components rho H => C.val) Subtype.val_injective

local instance : Fintype (Components rho H) := by
  letI := components_finite rho H
  exact Fintype.ofFinite _

omit [H.Normal] [Finite V] in
theorem components_independent :
    iSupIndep (fun C : Components rho H => C.val) :=
  (sSupIndep_iff _).mp (sSupIndep_isotypicComponents k[H] (restricted rho H).asModule)

omit [H.Normal] [Finite V] in
theorem components_sup_eq_top
    (hss : IsSemisimpleModule k[H] (restricted rho H).asModule) :
    (⨆ C : Components rho H, C.val) = ⊤ := by
  letI := hss
  exact (sSup_eq_iSup' _).symm.trans
    (sSup_isotypicComponents k[H] (restricted rho H).asModule)

def decomposition
    (hss : IsSemisimpleModule k[H] (restricted rho H).asModule) :
    ((C : Components rho H) → C.val) ≃ₗ[k[H]] (restricted rho H).asModule :=
  (DFinsupp.linearEquivFunOnFintype (R := k[H])
    (M := fun C : Components rho H => C.val)).symm.trans
      ((components_independent rho H).linearEquiv (components_sup_eq_top rho H hss))

theorem decomposition_single
    (hss : IsSemisimpleModule k[H] (restricted rho H).asModule)
    (C : Components rho H) (w : C.val) :
    decomposition rho H hss (Pi.single C w) = w.val := by
  apply ((components_independent rho H).linearEquiv
    (components_sup_eq_top rho H hss)).symm.injective
  change ((components_independent rho H).linearEquiv
    (components_sup_eq_top rho H hss)).symm
      (((components_independent rho H).linearEquiv
        (components_sup_eq_top rho H hss))
        ((DFinsupp.linearEquivFunOnFintype (R := k[H])
          (M := fun D : Components rho H => D.val)).symm (Pi.single C w))) = _
  rw [LinearEquiv.symm_apply_apply, iSupIndep.linearEquiv_symm_apply _ _ w.property]
  change ((DFinsupp.linearEquivFunOnFintype (R := k[H])
    (M := fun D : Components rho H => D.val)).symm (Pi.single C w)) =
      (DFinsupp.single C w : Π₀ D : Components rho H, D.val)
  exact DFinsupp.equivFunOnFintype_symm_single
    (β := fun D : Components rho H => D.val) C w

def coordinates
    (hss : IsSemisimpleModule k[H] (restricted rho H).asModule) :
    V ≃ₗ[k] ((C : Components rho H) → C.val) :=
  (restricted rho H).asModuleEquiv.symm.trans
    ((decomposition rho H hss).symm.restrictScalars k)

theorem coordinates_component
    (hss : IsSemisimpleModule k[H] (restricted rho H).asModule)
    (C : Components rho H) (w : C.val) :
    coordinates rho H hss ((restricted rho H).asModuleEquiv w.val) = Pi.single C w := by
  apply (decomposition rho H hss).injective
  change decomposition rho H hss ((decomposition rho H hss).symm w.val) = _
  rw [LinearEquiv.apply_symm_apply, decomposition_single]

theorem coordinates_symm_single
    (hss : IsSemisimpleModule k[H] (restricted rho H).asModule)
    (C : Components rho H) (w : C.val) :
    (coordinates rho H hss).symm (Pi.single C w) =
      (restricted rho H).asModuleEquiv w.val := by
  apply (coordinates rho H hss).injective
  rw [LinearEquiv.apply_symm_apply, coordinates_component]

theorem kernel_coordinate_zero
    (hss : IsSemisimpleModule k[H] (restricted rho H).asModule)
    (g : (componentPermutationHom rho H).ker) (v : V) (C : Components rho H)
    (hv : coordinates rho H hss v C = 0) :
    coordinates rho H hss (rho g.val v) C = 0 := by
  let E := coordinates rho H hss
  let F : ((D : Components rho H) → D.val) →ₗ[k]
      ((D : Components rho H) → D.val) :=
    E.toLinearMap.comp ((rho g.val).comp E.symm.toLinearMap)
  have hoff (D : Components rho H) (w : D.val) (hDC : D ≠ C) :
      F (Pi.single D w) C = 0 := by
    have hw : (restricted rho H).asModuleEquiv w.val ∈ space rho H D.val := w.property
    have hm := kernel_preserves_space rho H g.val g.property D _ hw
    let z : D.val := ⟨(restricted rho H).asModuleEquiv.symm
      (rho g.val ((restricted rho H).asModuleEquiv w.val)), hm⟩
    change E (rho g.val (E.symm (Pi.single D w))) C = 0
    rw [coordinates_symm_single]
    have he := congrFun (coordinates_component rho H hss D z) C
    change E (rho g.val ((restricted rho H).asModuleEquiv w.val)) C =
      (Pi.single D z : (D : Components rho H) → D.val) C at he
    rw [he]
    exact Pi.single_eq_of_ne (M := fun D : Components rho H => D.val) (Ne.symm hDC) z
  have he : F (E v) = E (rho g.val v) := by
    change E (rho g.val (E.symm (E v))) = E (rho g.val v)
    rw [LinearEquiv.symm_apply_apply]
  rw [← he]
  have hsum : F (E v) = ∑ D : Components rho H, F (Pi.single D (E v D)) := by
    rw [← map_sum, Finset.univ_sum_single]
  rw [hsum, Finset.sum_apply]
  apply Finset.sum_eq_zero
  intro D _
  by_cases hDC : D = C
  · subst D
    change F (Pi.single C (coordinates rho H hss v C)) C = 0
    rw [hv, Pi.single_zero, map_zero]
    rfl
  · exact hoff D (E v D) hDC

end SymmetricSubgroupAsymptotics.CFSGCliffordComponentCoordinates
