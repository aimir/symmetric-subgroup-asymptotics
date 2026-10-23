import SymmetricSubgroupAsymptotics.CFSGTwistedDFieldGeometry
import SymmetricSubgroupAsymptotics.CFSGQuadraticPolarFieldCoherence

/-! Removing the chosen actual field action leaves genuine linear
pieces. Its actual inverse is used: a separately chosen extension of
the inverse field automorphism need not be the inverse extension. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTwistedDFieldNormalization
open CFSGTwistedDFixedQuadraticSpace CFSGTwistedDFieldGeometry
open CFSGTwistedDPointStars CFSGTwistedDPlaneFamilyAction CFSGTwistedDPointOrthogonality
open CFSGTwistedA2FixedField CFSGOrthogonalDIndexQuadraticSubspacePoints CFSGSingularPlaneTriangle

local instance (n : ℕ) (q : CFSG.PrimePower) :
    Module.Finite (fixedField q) (fixedSpace n q) := Module.Finite.of_finite
local instance (q : CFSG.PrimePower) (sigma : fixedField q ≃+* fixedField q) :
    RingHomInvPair sigma.toRingHom sigma.symm.toRingHom := RingHomInvPair.of_ringEquiv sigma
local instance (q : CFSG.PrimePower) (sigma : fixedField q ≃+* fixedField q) :
    RingHomInvPair sigma.symm.toRingHom sigma.toRingHom := RingHomInvPair.of_ringEquiv_symm sigma

abbrev normalizedPoints (s : ℕ) (q : CFSG.PrimePower) (f : Equiv.Perm (SingularPoints s q))
    (sigma : fixedField q ≃+* fixedField q) := f.trans (pointEquiv s q sigma).symm
abbrev normalizedPlanes (s : ℕ) (q : CFSG.PrimePower) (l : Equiv.Perm (SingularPlanes s q))
    (sigma : fixedField q ≃+* fixedField q) := l.trans (planeEquiv s q sigma).symm

def normalizedPieceMap (s : ℕ) (q : CFSG.PrimePower) (f : Equiv.Perm (SingularPoints s q))
    (W : Subspaces (fixedQuadraticForm (s + 2) q)) (sigma : fixedField q ≃+* fixedField q)
    (F : SemilinearPiece (fixedQuadraticForm (s + 2) q) f W sigma) :
    W.val →ₗ[fixedField q] fixedSpace (s + 2) q where
  toFun x := (vectorEquiv (s + 2) q sigma).symm (F.map x)
  map_add' x y := by simp only [map_add]
  map_smul' a x := by
    change (vectorEquiv (s + 2) q sigma).symm (F.map (a • x)) =
      a • (vectorEquiv (s + 2) q sigma).symm (F.map x)
    rw [F.map.map_smulₛₗ, (vectorEquiv (s + 2) q sigma).symm.map_smulₛₗ]
    simp only [RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, RingEquiv.symm_apply_apply]

def normalizedPiece (s : ℕ) (q : CFSG.PrimePower) (f : Equiv.Perm (SingularPoints s q))
    (W : Subspaces (fixedQuadraticForm (s + 2) q)) (sigma : fixedField q ≃+* fixedField q)
    (F : SemilinearPiece (fixedQuadraticForm (s + 2) q) f W sigma) :
    SemilinearPiece (fixedQuadraticForm (s + 2) q) (normalizedPoints s q f sigma)
      W (RingEquiv.refl (fixedField q)) where
  map := normalizedPieceMap s q f W sigma F
  injective := (vectorEquiv (s + 2) q sigma).symm.injective.comp F.injective
  point x hx := by
    change Submodule.span (fixedField q) {(vectorEquiv (s + 2) q sigma).symm (F.map x)} =
      (f (ray (fixedQuadraticForm (s + 2) q) x.val (fun h => hx (Subtype.ext h))
        (W.property x.val x.property))).val.comap (vectorEquiv (s + 2) q sigma).toLinearMap
    rw [Submodule.comap_equiv_eq_map_symm, ← F.point x hx, Submodule.map_span, Set.image_singleton]
    rfl

theorem field_orthogonality (s : ℕ) (q : CFSG.PrimePower)
    (sigma : fixedField q ≃+* fixedField q) (P Q : SingularPoints s q) :
    PointOrthogonal s q (pointEquiv s q sigma P) (pointEquiv s q sigma Q) ↔
      PointOrthogonal s q P Q := by
  constructor
  · intro h x hx y hy
    apply sigma.injective
    rw [map_zero, ← polar_map]
    exact h _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
  · rintro h x ⟨u, hu, rfl⟩ y ⟨v, hv, rfl⟩
    change (fixedQuadraticForm (s + 2) q).polarBilin
      (vectorEquiv (s + 2) q sigma u) (vectorEquiv (s + 2) q sigma v) = 0
    rw [polar_map, h u hu v hv, map_zero]

theorem normalized_incidence (s : ℕ) (q : CFSG.PrimePower)
    (f : Equiv.Perm (SingularPoints s q)) (l : Equiv.Perm (SingularPlanes s q))
    (hinc : ∀ P L, (f P).val ≤ (l L).val ↔ P.val ≤ L.val)
    (sigma : fixedField q ≃+* fixedField q) (P : SingularPoints s q) (L : SingularPlanes s q) :
    (normalizedPoints s q f sigma P).val ≤ (normalizedPlanes s q l sigma L).val ↔ P.val ≤ L.val := by
  have he := incidence s q sigma ((pointEquiv s q sigma).symm (f P))
    ((planeEquiv s q sigma).symm (l L))
  simp only [Equiv.apply_symm_apply] at he
  exact he.symm.trans (hinc P L)

theorem normalized_orthogonality (s : ℕ) (q : CFSG.PrimePower)
    (f : Equiv.Perm (SingularPoints s q))
    (horth : ∀ P Q, PointOrthogonal s q (f P) (f Q) ↔ PointOrthogonal s q P Q)
    (sigma : fixedField q ≃+* fixedField q) (P Q : SingularPoints s q) :
    PointOrthogonal s q (normalizedPoints s q f sigma P) (normalizedPoints s q f sigma Q) ↔
      PointOrthogonal s q P Q := by
  have he := field_orthogonality s q sigma ((pointEquiv s q sigma).symm (f P))
    ((pointEquiv s q sigma).symm (f Q))
  simp only [Equiv.apply_symm_apply] at he
  exact he.symm.trans (horth P Q)

end SymmetricSubgroupAsymptotics.CFSGTwistedDFieldNormalization
