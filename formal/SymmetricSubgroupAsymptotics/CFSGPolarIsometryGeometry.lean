import SymmetricSubgroupAsymptotics.CFSGSingularSubspaceIsometry
import SymmetricSubgroupAsymptotics.CFSGPolarLocalFieldCoherence

/-! Literal linear isometries act reversibly on polar points and
planes. Postcomposition preserves actual semilinear representatives,
so geometric normalizations retain the already-proved local linearity. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGPolarIsometryGeometry
open CFSGPolarSubspacePoints CFSGSingularPlaneTriangle
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
variable (B : LinearMap.BilinForm K V) (e : V≃ₗ[K]V) (he : ∀x y,B (e x) (e y)=B x y)

include he in
theorem zeroOn_map_iff (P Q : Submodule K V) :
    ZeroOn B (P.map e.toLinearMap) (Q.map e.toLinearMap) ↔ ZeroOn B P Q := by
  constructor
  · intro h x hx y hy
    rw [←he x y]
    exact h _ ⟨x,hx,rfl⟩ _ ⟨y,hy,rfl⟩
  · rintro h x ⟨x',hx,rfl⟩ y ⟨y',hy,rfl⟩
    exact (he x' y').trans (h x' hx y' hy)

def pointEquiv : Points B≃Points B :=
  Equiv.subtypeEquiv (Submodule.orderIsoMapComap e).toEquiv (fun P=>by
    change (Module.finrank K P=1 ∧ ZeroOn B P P) ↔
      (Module.finrank K (P.map e.toLinearMap)=1 ∧ ZeroOn B (P.map e.toLinearMap) (P.map e.toLinearMap))
    rw [e.finrank_map_eq,zeroOn_map_iff B e he])

def planeEquiv : Planes B≃Planes B :=
  Equiv.subtypeEquiv (Submodule.orderIsoMapComap e).toEquiv (fun P=>by
    change (Module.finrank K P=2 ∧ ZeroOn B P P) ↔
      (Module.finrank K (P.map e.toLinearMap)=2 ∧ ZeroOn B (P.map e.toLinearMap) (P.map e.toLinearMap))
    rw [e.finrank_map_eq,zeroOn_map_iff B e he])

theorem incidence (P : Points B) (L : Planes B) :
    (pointEquiv B e he P).val≤(planeEquiv B e he L).val ↔ P.val≤L.val :=
  Submodule.map_le_map_iff_of_injective e.injective _ _

theorem orthogonality (P Q : Points B) :
    ZeroOn B (pointEquiv B e he P).val (pointEquiv B e he Q).val ↔ ZeroOn B P.val Q.val :=
  zeroOn_map_iff B e he P.val Q.val

def postcomposePiece (f : Points B≃Points B) (W : Subspaces B) (σ : K≃+*K)
    (F : SemilinearPiece B f W σ) : SemilinearPiece B (f.trans (pointEquiv B e he)) W σ where
  map := e.toLinearMap.comp F.map
  injective := e.injective.comp F.injective
  point x hx := by
    change Submodule.span K {e (F.map x)}=
      (f (ray B x.val (fun h=>hx (Subtype.ext h)) (W.property x.val x.property x.val x.property))).val.map e.toLinearMap
    rw [←F.point x hx,Submodule.map_span,Set.image_singleton]
    rfl

end SymmetricSubgroupAsymptotics.CFSGPolarIsometryGeometry
