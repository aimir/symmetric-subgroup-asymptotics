import SymmetricSubgroupAsymptotics.CFSGOrthogonalBOriginalGlobalField
import SymmetricSubgroupAsymptotics.CFSGFiniteFieldSemilinearDimension

/-! Coordinate field automorphisms act on the SAME original B singular
points and planes. The Gram pairing is transported by the literal field
map, and dimensions by an actual finite-field cardinal bijection. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalBFieldGeometry
open CFSGOrthogonalBSerreMatrices CFSGPolarSubspacePoints CFSGSingularPlaneTriangle
variable {K : Type} [Field K]
local instance (s : K≃+*K) : RingHomInvPair s.toRingHom s.symm.toRingHom :=
  RingHomInvPair.of_ringEquiv s
local instance (s : K≃+*K) : RingHomInvPair s.symm.toRingHom s.toRingHom :=
  RingHomInvPair.of_ringEquiv_symm s

abbrev vectorEquiv (σ : K≃+*K) (n : ℕ) :=
  CFSGProjectiveFieldAction.coordinateEquiv (n:=Index n) σ

theorem pairing_map (σ : K≃+*K) (n : ℕ) (x y : Index n→K) :
    (gram K n).toBilin' (vectorEquiv σ n x) (vectorEquiv σ n y)=
      σ ((gram K n).toBilin' x y) := by
  have hg : ∀i j : Index n,σ (gram K n i j)=gram K n i j := by
    intro i j
    have htwo : σ (2 : K) = 2 := by
      rw [show (2 : K)=1+1 by ring,map_add,map_one]
    rcases i with (i|i)|⟨⟩ <;> rcases j with (j|j)|⟨⟩ <;> simp only [gram]
    all_goals try split_ifs
    all_goals simp only [map_zero,map_one,htwo]
  change (gram K n).toBilin' (σ ∘ x) (σ ∘ y)=σ ((gram K n).toBilin' x y)
  simp only [Matrix.toBilin'_apply,map_sum,map_mul,hg,Function.comp_apply]

theorem zeroOn_map_iff (σ : K≃+*K) (n : ℕ) (P Q : Submodule K (Index n→K)) :
    ZeroOn (gram K n).toBilin' (P.map (vectorEquiv σ n).toLinearMap)
      (Q.map (vectorEquiv σ n).toLinearMap) ↔ ZeroOn (gram K n).toBilin' P Q := by
  constructor
  · intro h x hx y hy
    apply σ.injective
    rw [map_zero,←pairing_map σ n x y]
    exact h _ ⟨x,hx,rfl⟩ _ ⟨y,hy,rfl⟩
  · rintro h x ⟨x',hx,rfl⟩ y ⟨y',hy,rfl⟩
    change (gram K n).toBilin' (vectorEquiv σ n x') (vectorEquiv σ n y')=0
    rw [pairing_map,h x' hx y' hy,map_zero]

variable [Finite K]

def pointEquiv (σ : K≃+*K) (n : ℕ) : Points (gram K n).toBilin'≃Points (gram K n).toBilin' :=
  Equiv.subtypeEquiv (Submodule.orderIsoMapComap (vectorEquiv σ n)).toEquiv (fun P=>by
    change (Module.finrank K P=1 ∧ ZeroOn (gram K n).toBilin' P P) ↔
      (Module.finrank K (P.map (vectorEquiv σ n).toLinearMap)=1 ∧
        ZeroOn (gram K n).toBilin' (P.map (vectorEquiv σ n).toLinearMap)
          (P.map (vectorEquiv σ n).toLinearMap))
    rw [CFSGFiniteFieldSemilinearDimension.finrank_map,zeroOn_map_iff])

def planeEquiv (σ : K≃+*K) (n : ℕ) : Planes (gram K n).toBilin'≃Planes (gram K n).toBilin' :=
  Equiv.subtypeEquiv (Submodule.orderIsoMapComap (vectorEquiv σ n)).toEquiv (fun P=>by
    change (Module.finrank K P=2 ∧ ZeroOn (gram K n).toBilin' P P) ↔
      (Module.finrank K (P.map (vectorEquiv σ n).toLinearMap)=2 ∧
        ZeroOn (gram K n).toBilin' (P.map (vectorEquiv σ n).toLinearMap)
          (P.map (vectorEquiv σ n).toLinearMap))
    rw [CFSGFiniteFieldSemilinearDimension.finrank_map,zeroOn_map_iff])

theorem incidence (σ : K≃+*K) (n : ℕ) (P : Points (gram K n).toBilin')
    (L : Planes (gram K n).toBilin') :
    (pointEquiv σ n P).val≤(planeEquiv σ n L).val ↔ P.val≤L.val :=
  Submodule.map_le_map_iff_of_injective (vectorEquiv σ n).injective _ _

theorem orthogonality (σ : K≃+*K) (n : ℕ) (P Q : Points (gram K n).toBilin') :
    ZeroOn (gram K n).toBilin' (pointEquiv σ n P).val (pointEquiv σ n Q).val ↔
      ZeroOn (gram K n).toBilin' P.val Q.val := zeroOn_map_iff σ n P.val Q.val

end SymmetricSubgroupAsymptotics.CFSGOrthogonalBFieldGeometry
