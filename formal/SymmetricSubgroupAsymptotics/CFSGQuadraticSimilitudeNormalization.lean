import SymmetricSubgroupAsymptotics.CFSGQuadraticSimilitudeGeometry
import SymmetricSubgroupAsymptotics.CFSGQuadraticPolarPointFunctionals

/-! Postcomposition by the inverse of a genuine ambient similitude
preserves the literal polar zero relation. If it extends a local
representative, it fixes every actual point of that representative's
domain. These facts do not require the similitude to be an inner action. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGQuadraticSimilitudeNormalization
open CFSGOrthogonalDIndexQuadraticSubspacePoints CFSGSingularPlaneTriangle
open CFSGQuadraticSimilitudeGeometry
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

theorem polar_similitude (Q : QuadraticForm K V) (L : V ≃ₗ[K] V)
    (c : K) (hQ : ∀ x, Q (L x) = c * Q x) (x y : V) :
    Q.polarBilin (L x) (L y) = c * Q.polarBilin x y := by
  change Q (L x + L y) - Q (L x) - Q (L y) = c * (Q (x + y) - Q x - Q y)
  rw [← L.map_add, hQ, hQ, hQ]
  ring

theorem pointEquiv_zeroOn_iff (Q : QuadraticForm K V) (L : V ≃ₗ[K] V)
    (c : K) (hc : c ≠ 0) (hQ : ∀ x, Q (L x) = c * Q x) (P R : Points Q) :
    ZeroOn Q.polarBilin (pointEquiv Q L c hc hQ P).val
      (pointEquiv Q L c hc hQ R).val ↔ ZeroOn Q.polarBilin P.val R.val := by
  constructor
  · intro h x hx y hy
    have he := h (L x) ⟨x, hx, rfl⟩ (L y) ⟨y, hy, rfl⟩
    rw [polar_similitude Q L c hQ] at he
    exact (mul_eq_zero.mp he).resolve_left hc
  · rintro h x ⟨u, hu, rfl⟩ y ⟨v, hv, rfl⟩
    change Q.polarBilin (L u) (L v) = 0
    rw [polar_similitude Q L c hQ, h u hu v hv, mul_zero]

theorem postcompose_orthogonality (Q : QuadraticForm K V) (L : V ≃ₗ[K] V)
    (c : K) (hc : c ≠ 0) (hQ : ∀ x, Q (L x) = c * Q x)
    (f : Points Q ≃ Points Q)
    (hf : ∀ P R, ZeroOn Q.polarBilin (f P).val (f R).val ↔ ZeroOn Q.polarBilin P.val R.val)
    (P R : Points Q) :
    ZeroOn Q.polarBilin (f.trans (pointEquiv Q L c hc hQ) P).val
      (f.trans (pointEquiv Q L c hc hQ) R).val ↔ ZeroOn Q.polarBilin P.val R.val :=
  (pointEquiv_zeroOn_iff Q L c hc hQ (f P) (f R)).trans (hf P R)

theorem inverse_extension_fixes_points (Q : QuadraticForm K V) (L : V ≃ₗ[K] V)
    (c : K) (hc : c ≠ 0) (hQ : ∀ x, Q (L x) = c * Q x)
    (f : Points Q ≃ Points Q) (W : Subspaces Q)
    (F : SemilinearPiece Q f W (RingEquiv.refl K))
    (hext : ∀ x : W.val, L x.val = F.map x) (P : Points Q) (hPW : P.val ≤ W.val) :
    f.trans (pointEquiv Q L.symm c⁻¹ (inv_ne_zero hc) (inverse_quadratic Q L c hc hQ)) P = P := by
  obtain ⟨v, hv, hv0⟩ := point_nonzero Q P
  let x : W.val := ⟨v, hPW hv⟩
  have hx0 : x ≠ 0 := fun h => hv0 (congrArg Subtype.val h)
  have hP : ray Q v hv0 (W.property v (hPW hv)) = P :=
    Subtype.ext (point_span Q P v hv hv0)
  have hF := F.point x hx0
  change Submodule.span K {F.map x} =
    (f (ray Q v hv0 (W.property v (hPW hv)))).val at hF
  rw [hP, ← hext x] at hF
  apply Subtype.ext
  change (f P).val.map L.symm.toLinearMap = P.val
  rw [← hF, Submodule.map_span, Set.image_singleton]
  change Submodule.span K {L.symm (L v)} = P.val
  rw [L.symm_apply_apply]
  exact point_span Q P v hv hv0

end SymmetricSubgroupAsymptotics.CFSGQuadraticSimilitudeNormalization
