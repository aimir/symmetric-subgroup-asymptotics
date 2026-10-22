import SymmetricSubgroupAsymptotics.CFSGCliffordComponentCoordinates
import Mathlib.LinearAlgebra.Dimension.Constructions

/-! Dimension accounting for the actual isotypic block decomposition,
with scalar-restriction carriers explicitly identified. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical MonoidAlgebra

namespace SymmetricSubgroupAsymptotics.CFSGCliffordComponentDimensions
open CFSGCliffordIsotypicTransport CFSGCliffordIsotypicPermutation
  CFSGCliffordComponentSpaces CFSGCliffordComponentCoordinates

variable {k G V : Type} [Field k] [Group G] [AddCommGroup V] [Module k V]
  (rho : Representation k G V) (H : Subgroup G) [H.Normal]

local instance [Finite V] : Fintype (Components rho H) := by
  letI := components_finite rho H
  exact Fintype.ofFinite _

def spaceEquiv (S : Submodule k[H] (restricted rho H).asModule) :
    S ≃ₗ[k] space rho H S where
  toFun x := ⟨(restricted rho H).asModuleEquiv x.val, x.property⟩
  invFun x := ⟨(restricted rho H).asModuleEquiv.symm x.val, x.property⟩
  left_inv x := Subtype.ext ((restricted rho H).asModuleEquiv.symm_apply_apply x.val)
  right_inv x := Subtype.ext ((restricted rho H).asModuleEquiv.apply_symm_apply x.val)
  map_add' x y := Subtype.ext ((restricted rho H).asModuleEquiv.map_add x.val y.val)
  map_smul' a x := Subtype.ext ((restricted rho H).asModuleEquiv.map_smul a x.val)

theorem component_module_finrank_eq [Finite G] [FiniteDimensional k V]
    (hrho : Representation.IsIrreducible rho) (C D : Components rho H) :
    Module.finrank k C.val = Module.finrank k D.val :=
  (spaceEquiv rho H C.val).finrank_eq.trans
    ((component_finrank_eq rho H hrho C D).trans (spaceEquiv rho H D.val).finrank_eq.symm)

omit [H.Normal] in
theorem finrank_eq_component_sum [Finite V] [FiniteDimensional k V]
    (hss : IsSemisimpleModule k[H] (restricted rho H).asModule) :
    Module.finrank k V =
      ∑ C : Components rho H, Module.finrank k C.val := by
  letI : ∀ C : Components rho H, FiniteDimensional k C.val := fun C =>
    FiniteDimensional.of_injective (C.val.subtype.restrictScalars k)
      C.val.subtype_injective
  exact (coordinates rho H hss).finrank_eq.trans (Module.finrank_pi_fintype k)

theorem component_count_mul_finrank [Finite G] [Finite V] [FiniteDimensional k V]
    (hrho : Representation.IsIrreducible rho)
    (hss : IsSemisimpleModule k[H] (restricted rho H).asModule)
    (C : Components rho H) :
    Nat.card (Components rho H) * Module.finrank k C.val = Module.finrank k V := by
  rw [finrank_eq_component_sum rho H hss]
  calc
    Nat.card (Components rho H) * Module.finrank k C.val =
        ∑ _D : Components rho H, Module.finrank k C.val := by
          simp only [Finset.sum_const, Finset.card_univ, Nat.card_eq_fintype_card,
            nsmul_eq_mul, Nat.cast_id]
    _ = ∑ D : Components rho H, Module.finrank k D.val :=
      Finset.sum_congr rfl (fun D _ => component_module_finrank_eq rho H hrho C D)

end SymmetricSubgroupAsymptotics.CFSGCliffordComponentDimensions
