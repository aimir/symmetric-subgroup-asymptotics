import SymmetricSubgroupAsymptotics.CFSGOrthogonalDFieldGeometry
import SymmetricSubgroupAsymptotics.CFSGQuadraticPolarFieldCoherence

/-! Removing the proved global field component leaves actual linear
representatives on every maximal original singular subspace. The
normalization acts on the original points and planes and preserves their
literal incidence and orthogonality. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDFieldGeometry
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDIndexBundledQuadratic CFSGOrthogonalDIndexQuadraticSubspacePoints CFSGSingularPlaneTriangle
variable {K : Type} [Field K] [Finite K]
local instance (s : K≃+*K) : RingHomInvPair s.toRingHom s.symm.toRingHom :=
  RingHomInvPair.of_ringEquiv s
local instance (s : K≃+*K) : RingHomInvPair s.symm.toRingHom s.toRingHom :=
  RingHomInvPair.of_ringEquiv_symm s

abbrev normalizedPoints (n : ℕ) (f : Points (splitQuadraticForm K n)≃Points (splitQuadraticForm K n))
    (σ : K≃+*K) := f.trans (pointEquiv σ.symm n)
abbrev normalizedPlanes (n : ℕ) (l : Planes (splitQuadraticForm K n)≃Planes (splitQuadraticForm K n))
    (σ : K≃+*K) := l.trans (planeEquiv σ.symm n)

def normalizedPieceMap (n : ℕ) (f : Points (splitQuadraticForm K n)≃Points (splitQuadraticForm K n))
    (W : Subspaces (splitQuadraticForm K n)) (σ : K≃+*K)
    (F : SemilinearPiece (splitQuadraticForm K n) f W σ) : W.val→ₗ[K](Index n→K) where
  toFun x := vectorEquiv σ.symm n (F.map x)
  map_add' x y := by simp only [map_add]
  map_smul' a x := by
    change vectorEquiv σ.symm n (F.map (a•x))=a•vectorEquiv σ.symm n (F.map x)
    rw [F.map.map_smulₛₗ, (vectorEquiv σ.symm n).map_smulₛₗ]
    simp only [RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, RingEquiv.symm_apply_apply]

def normalizedPiece (n : ℕ) (f : Points (splitQuadraticForm K n)≃Points (splitQuadraticForm K n))
    (W : Subspaces (splitQuadraticForm K n)) (σ : K≃+*K)
    (F : SemilinearPiece (splitQuadraticForm K n) f W σ) :
    SemilinearPiece (splitQuadraticForm K n) (normalizedPoints n f σ) W (RingEquiv.refl K) where
  map := normalizedPieceMap n f W σ F
  injective := (vectorEquiv σ.symm n).injective.comp F.injective
  point x hx := by
    change Submodule.span K {vectorEquiv σ.symm n (F.map x)}=
      ((f (ray (splitQuadraticForm K n) x.val (fun h=>hx (Subtype.ext h))
        (W.property x.val x.property))).val.map
        (vectorEquiv σ.symm n).toLinearMap)
    rw [←F.point x hx,Submodule.map_span,Set.image_singleton]
    rfl

theorem normalized_incidence (n : ℕ)
    (f : Points (splitQuadraticForm K n)≃Points (splitQuadraticForm K n))
    (l : Planes (splitQuadraticForm K n)≃Planes (splitQuadraticForm K n))
    (hinc : ∀P L,(f P).val≤(l L).val ↔ P.val≤L.val) (σ : K≃+*K)
    (P : Points (splitQuadraticForm K n)) (L : Planes (splitQuadraticForm K n)) :
    (normalizedPoints n f σ P).val≤(normalizedPlanes n l σ L).val ↔ P.val≤L.val :=
  (incidence σ.symm n (f P) (l L)).trans (hinc P L)

theorem normalized_orthogonality (n : ℕ)
    (f : Points (splitQuadraticForm K n)≃Points (splitQuadraticForm K n))
    (horth : ∀P Q,ZeroOn (splitQuadraticForm K n).polarBilin (f P).val (f Q).val ↔
      ZeroOn (splitQuadraticForm K n).polarBilin P.val Q.val) (σ : K≃+*K)
    (P Q : Points (splitQuadraticForm K n)) :
    ZeroOn (splitQuadraticForm K n).polarBilin (normalizedPoints n f σ P).val
      (normalizedPoints n f σ Q).val ↔ ZeroOn (splitQuadraticForm K n).polarBilin P.val Q.val :=
  (orthogonality σ.symm n (f P) (f Q)).trans (horth P Q)

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDFieldGeometry
