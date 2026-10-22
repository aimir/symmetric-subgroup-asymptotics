import SymmetricSubgroupAsymptotics.CFSGOrthogonalBFieldGeometry

/-! Removing the proved global field component leaves actual linear
representatives on every maximal original singular subspace. The
normalization acts on the original points and planes and preserves their
literal incidence and orthogonality. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalBFieldGeometry
open CFSGOrthogonalBSerreMatrices CFSGPolarSubspacePoints CFSGSingularPlaneTriangle
variable {K : Type} [Field K] [Finite K]
local instance (s : K≃+*K) : RingHomInvPair s.toRingHom s.symm.toRingHom :=
  RingHomInvPair.of_ringEquiv s
local instance (s : K≃+*K) : RingHomInvPair s.symm.toRingHom s.toRingHom :=
  RingHomInvPair.of_ringEquiv_symm s

abbrev normalizedPoints (n : ℕ) (f : Points (gram K n).toBilin'≃Points (gram K n).toBilin')
    (σ : K≃+*K) := f.trans (pointEquiv σ.symm n)
abbrev normalizedPlanes (n : ℕ) (l : Planes (gram K n).toBilin'≃Planes (gram K n).toBilin')
    (σ : K≃+*K) := l.trans (planeEquiv σ.symm n)

def normalizedPieceMap (n : ℕ) (f : Points (gram K n).toBilin'≃Points (gram K n).toBilin')
    (W : Subspaces (gram K n).toBilin') (σ : K≃+*K)
    (F : SemilinearPiece (gram K n).toBilin' f W σ) : W.val→ₗ[K](Index n→K) where
  toFun x := vectorEquiv σ.symm n (F.map x)
  map_add' x y := by simp only [map_add]
  map_smul' a x := by
    change vectorEquiv σ.symm n (F.map (a•x))=a•vectorEquiv σ.symm n (F.map x)
    rw [F.map.map_smulₛₗ, (vectorEquiv σ.symm n).map_smulₛₗ]
    simp only [RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, RingEquiv.symm_apply_apply]

def normalizedPiece (n : ℕ) (f : Points (gram K n).toBilin'≃Points (gram K n).toBilin')
    (W : Subspaces (gram K n).toBilin') (σ : K≃+*K)
    (F : SemilinearPiece (gram K n).toBilin' f W σ) :
    SemilinearPiece (gram K n).toBilin' (normalizedPoints n f σ) W (RingEquiv.refl K) where
  map := normalizedPieceMap n f W σ F
  injective := (vectorEquiv σ.symm n).injective.comp F.injective
  point x hx := by
    change Submodule.span K {vectorEquiv σ.symm n (F.map x)}=
      ((f (ray (gram K n).toBilin' x.val (fun h=>hx (Subtype.ext h))
        (W.property x.val x.property x.val x.property))).val.map
        (vectorEquiv σ.symm n).toLinearMap)
    rw [←F.point x hx,Submodule.map_span,Set.image_singleton]
    rfl

theorem normalized_incidence (n : ℕ)
    (f : Points (gram K n).toBilin'≃Points (gram K n).toBilin')
    (l : Planes (gram K n).toBilin'≃Planes (gram K n).toBilin')
    (hinc : ∀P L,(f P).val≤(l L).val ↔ P.val≤L.val) (σ : K≃+*K)
    (P : Points (gram K n).toBilin') (L : Planes (gram K n).toBilin') :
    (normalizedPoints n f σ P).val≤(normalizedPlanes n l σ L).val ↔ P.val≤L.val :=
  (incidence σ.symm n (f P) (l L)).trans (hinc P L)

theorem normalized_orthogonality (n : ℕ)
    (f : Points (gram K n).toBilin'≃Points (gram K n).toBilin')
    (horth : ∀P Q,ZeroOn (gram K n).toBilin' (f P).val (f Q).val ↔
      ZeroOn (gram K n).toBilin' P.val Q.val) (σ : K≃+*K)
    (P Q : Points (gram K n).toBilin') :
    ZeroOn (gram K n).toBilin' (normalizedPoints n f σ P).val
      (normalizedPoints n f σ Q).val ↔ ZeroOn (gram K n).toBilin' P.val Q.val :=
  (orthogonality σ.symm n (f P) (f Q)).trans (horth P Q)

end SymmetricSubgroupAsymptotics.CFSGOrthogonalBFieldGeometry

namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalBGlobalField
open CFSGOrthogonalBSerreMatrices CFSGPolarSubspacePoints CFSGOrthogonalBFieldGeometry
open CFSGSingularPlaneTriangle
variable (K : Type) [Field K] [Finite K]

theorem exists_linear_normalization (h2 : (2 : K)≠0) (s : ℕ)
    (f : Points (gram K (s+3)).toBilin'≃Points (gram K (s+3)).toBilin')
    (l : Planes (gram K (s+3)).toBilin'≃Planes (gram K (s+3)).toBilin')
    (hinc : ∀P L,(f P).val≤(l L).val ↔ P.val≤L.val)
    (horth : ∀P Q,ZeroOn (gram K (s+3)).toBilin' (f P).val (f Q).val ↔
      ZeroOn (gram K (s+3)).toBilin' P.val Q.val) :
    ∃σ : K≃+*K,∀W : Subspaces (gram K (s+3)).toBilin',
      Module.finrank K W.val=s+3 → Nonempty (SemilinearPiece (gram K (s+3)).toBilin'
        (normalizedPoints (s+3) f σ) W (RingEquiv.refl K)) := by
  obtain ⟨σ,hσ⟩ := exists_global_field K h2 s f l hinc horth
  exact ⟨σ,fun W hd=>⟨normalizedPiece (s+3) f W σ (Classical.choice (hσ W hd))⟩⟩

end SymmetricSubgroupAsymptotics.CFSGOrthogonalBGlobalField
