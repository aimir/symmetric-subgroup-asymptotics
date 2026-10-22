import SymmetricSubgroupAsymptotics.CFSGQuadraticPolarFieldCoherence

/-! Genuine quadratic similitudes act on literal Q-singular points and
planes. Their zero loci and polar orthogonality are transported with an
actual nonzero multiplier, retaining characteristic-two quadratic data.
Postcomposition transports actual semilinear representatives as well. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGQuadraticSimilitudeGeometry
open CFSGOrthogonalDIndexQuadraticSubspacePoints
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
variable (q : QuadraticForm K V) (L : V≃ₗ[K]V) (c : K) (hc : c≠0)
  (hQ : ∀x,q (L x)=c*q x)
include hc hQ

omit [FiniteDimensional K V] in
theorem inverse_quadratic (x : V) : q (L.symm x)=c⁻¹*q x := by
  have h := hQ (L.symm x)
  rw [L.apply_symm_apply] at h
  rw [h,←mul_assoc,inv_mul_cancel₀ hc,one_mul]

theorem singular_map_iff (W : Submodule K V) :
    (∀x∈W.map L.toLinearMap,q x=0) ↔ ∀x∈W,q x=0 := by
  constructor
  · intro h x hx
    have he := h (L x) ⟨x,hx,rfl⟩
    rw [hQ] at he
    exact (mul_eq_zero.mp he).resolve_left hc
  · rintro h x ⟨v,hv,rfl⟩
    change q (L v)=0
    rw [hQ,h v hv,mul_zero]

def pointEquiv : Points q≃Points q :=
  Equiv.subtypeEquiv (Submodule.orderIsoMapComap L).toEquiv (fun P=>by
    change (Module.finrank K P=1 ∧ ∀x∈P,q x=0) ↔
      (Module.finrank K (P.map L.toLinearMap)=1 ∧ ∀x∈P.map L.toLinearMap,q x=0)
    rw [L.finrank_map_eq,singular_map_iff q L c hc hQ])

def planeEquiv : Planes q≃Planes q :=
  Equiv.subtypeEquiv (Submodule.orderIsoMapComap L).toEquiv (fun P=>by
    change (Module.finrank K P=2 ∧ ∀x∈P,q x=0) ↔
      (Module.finrank K (P.map L.toLinearMap)=2 ∧ ∀x∈P.map L.toLinearMap,q x=0)
    rw [L.finrank_map_eq,singular_map_iff q L c hc hQ])

def postcomposePiece (f : Points q≃Points q) (W : Subspaces q) (σ : K≃+*K)
    (F : SemilinearPiece q f W σ) :
    SemilinearPiece q (f.trans (pointEquiv q L c hc hQ)) W σ where
  map := L.toLinearMap.comp F.map
  injective := L.injective.comp F.injective
  point x hx := by
    change Submodule.span K {L (F.map x)}=
      (f (ray q x.val (fun h=>hx (Subtype.ext h)) (W.property x.val x.property))).val.map L.toLinearMap
    rw [←F.point x hx,Submodule.map_span,Set.image_singleton]
    rfl

end SymmetricSubgroupAsymptotics.CFSGQuadraticSimilitudeGeometry
