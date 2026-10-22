import SymmetricSubgroupAsymptotics.CFSGPolarSubspacePoints

/-! Natural isometries transport literal singular submodules and
preserve their dimension. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGPolarSubspacePoints
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
variable (B : LinearMap.BilinForm K V) (e : V≃ₗ[K]V) (he : ∀x y,B (e x) (e y)=B x y)

def isometrySubspace (W : Subspaces B) : Subspaces B :=
  ⟨W.val.map e.toLinearMap,by
    rintro x ⟨x',hx,rfl⟩ y ⟨y',hy,rfl⟩
    exact (he x' y').trans (W.property x' hx y' hy)⟩

theorem isometrySubspace_finrank (W : Subspaces B) :
    Module.finrank K (isometrySubspace B e he W).val=Module.finrank K W.val :=
  e.finrank_map_eq W.val

end SymmetricSubgroupAsymptotics.CFSGPolarSubspacePoints
