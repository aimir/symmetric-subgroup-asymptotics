import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexBundledQuadratic
import SymmetricSubgroupAsymptotics.CFSGQuadraticPolarPointFunctionals
import SymmetricSubgroupAsymptotics.CFSGProjectiveFieldAction
import SymmetricSubgroupAsymptotics.CFSGFiniteFieldSemilinearDimension

/-! Coordinate field automorphisms preserve the SAME split quadratic form,
up to applying the field map to its value. The induced original singular
point and plane actions retain literal quadratic zero in characteristic two. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDFieldGeometry
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDIndexQuadraticForm
open CFSGOrthogonalDIndexBundledQuadratic CFSGOrthogonalDIndexPolarForm
open CFSGOrthogonalDIndexQuadraticSubspacePoints CFSGSingularPlaneTriangle
variable {K : Type} [Field K]
local instance (s : K≃+*K) : RingHomInvPair s.toRingHom s.symm.toRingHom :=
  RingHomInvPair.of_ringEquiv s
local instance (s : K≃+*K) : RingHomInvPair s.symm.toRingHom s.toRingHom :=
  RingHomInvPair.of_ringEquiv_symm s

abbrev vectorEquiv (σ : K≃+*K) (r : ℕ) :=
  CFSGProjectiveFieldAction.coordinateEquiv (n:=Index r) σ

theorem quadratic_map (σ : K≃+*K) (r : ℕ) (x : Index r→K) :
    splitQuadraticForm K r (vectorEquiv σ r x)=σ (splitQuadraticForm K r x) := by
  simp only [splitQuadraticForm_apply]
  change (∑i : Fin r,σ (x (Sum.inl i))*σ (x (Sum.inr i)))=
    σ (∑i : Fin r,x (Sum.inl i)*x (Sum.inr i))
  simp only [map_sum,map_mul]

theorem pairing_map (σ : K≃+*K) (r : ℕ) (x y : Index r→K) :
    (splitQuadraticForm K r).polarBilin (vectorEquiv σ r x) (vectorEquiv σ r y)=
      σ ((splitQuadraticForm K r).polarBilin x y) := by
  change splitQuadraticForm K r (vectorEquiv σ r x+vectorEquiv σ r y)-
    splitQuadraticForm K r (vectorEquiv σ r x)-
    splitQuadraticForm K r (vectorEquiv σ r y)=_
  rw [←map_add,quadratic_map,quadratic_map,quadratic_map,←map_sub,←map_sub]
  rfl

theorem singular_map_iff (σ : K≃+*K) (r : ℕ) (W : Submodule K (Index r→K)) :
    (∀x∈W.map (vectorEquiv σ r).toLinearMap,splitQuadraticForm K r x=0) ↔
      ∀x∈W,splitQuadraticForm K r x=0 := by
  constructor
  · intro h x hx
    apply σ.injective
    rw [map_zero,←quadratic_map]
    exact h _ ⟨x,hx,rfl⟩
  · rintro h x ⟨v,hv,rfl⟩
    change splitQuadraticForm K r (vectorEquiv σ r v)=0
    rw [quadratic_map,h v hv,map_zero]

theorem zeroOn_map_iff (σ : K≃+*K) (r : ℕ) (P R : Submodule K (Index r→K)) :
    ZeroOn (splitQuadraticForm K r).polarBilin
      (P.map (vectorEquiv σ r).toLinearMap) (R.map (vectorEquiv σ r).toLinearMap) ↔
      ZeroOn (splitQuadraticForm K r).polarBilin P R := by
  constructor
  · intro h x hx y hy
    apply σ.injective
    rw [map_zero,←pairing_map]
    exact h _ ⟨x,hx,rfl⟩ _ ⟨y,hy,rfl⟩
  · rintro h x ⟨u,hu,rfl⟩ y ⟨v,hv,rfl⟩
    change (splitQuadraticForm K r).polarBilin (vectorEquiv σ r u) (vectorEquiv σ r v)=0
    rw [pairing_map,h u hu v hv,map_zero]

variable [Finite K]

def pointEquiv (σ : K≃+*K) (r : ℕ) :
    Points (splitQuadraticForm K r)≃Points (splitQuadraticForm K r) :=
  Equiv.subtypeEquiv (Submodule.orderIsoMapComap (vectorEquiv σ r)).toEquiv (fun P=>by
    change (Module.finrank K P=1 ∧ ∀x∈P,splitQuadraticForm K r x=0) ↔
      (Module.finrank K (P.map (vectorEquiv σ r).toLinearMap)=1 ∧
        ∀x∈P.map (vectorEquiv σ r).toLinearMap,splitQuadraticForm K r x=0)
    rw [CFSGFiniteFieldSemilinearDimension.finrank_map,singular_map_iff])

def planeEquiv (σ : K≃+*K) (r : ℕ) :
    Planes (splitQuadraticForm K r)≃Planes (splitQuadraticForm K r) :=
  Equiv.subtypeEquiv (Submodule.orderIsoMapComap (vectorEquiv σ r)).toEquiv (fun P=>by
    change (Module.finrank K P=2 ∧ ∀x∈P,splitQuadraticForm K r x=0) ↔
      (Module.finrank K (P.map (vectorEquiv σ r).toLinearMap)=2 ∧
        ∀x∈P.map (vectorEquiv σ r).toLinearMap,splitQuadraticForm K r x=0)
    rw [CFSGFiniteFieldSemilinearDimension.finrank_map,singular_map_iff])

theorem incidence (σ : K≃+*K) (r : ℕ) (P : Points (splitQuadraticForm K r))
    (L : Planes (splitQuadraticForm K r)) :
    (pointEquiv σ r P).val≤(planeEquiv σ r L).val ↔ P.val≤L.val :=
  Submodule.map_le_map_iff_of_injective (vectorEquiv σ r).injective _ _

theorem orthogonality (σ : K≃+*K) (r : ℕ) (P R : Points (splitQuadraticForm K r)) :
    ZeroOn (splitQuadraticForm K r).polarBilin (pointEquiv σ r P).val
      (pointEquiv σ r R).val ↔ ZeroOn (splitQuadraticForm K r).polarBilin P.val R.val :=
  zeroOn_map_iff σ r P.val R.val

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDFieldGeometry
