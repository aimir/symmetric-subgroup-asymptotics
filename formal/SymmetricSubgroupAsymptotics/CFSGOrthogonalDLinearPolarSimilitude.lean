import SymmetricSubgroupAsymptotics.CFSGOrthogonalDLinearPieceSimilitude
import SymmetricSubgroupAsymptotics.CFSGQuadraticSimilitudeGeometry
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDNegativeDilation

/-! Whole linear polar realization for the original split quadratic
space, uniformly in characteristic. Opposed representatives first glue
to an actual similitude. Removing it fixes both halves; the proved common
scalar then gives one negative dilation on EVERY singular point. There
is no orthogonal recognition or arbitrary automorphism-lift premise. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDLinearPolarSimilitude
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDIndexPositiveSpace
open CFSGOrthogonalDIndexBundledQuadratic CFSGOrthogonalDIndexQuadraticSubspacePoints
open CFSGOrthogonalDOpposedSpaces CFSGOrthogonalDLinearPieceSimilitude
open CFSGSingularPlaneTriangle
variable (K : Type) [Field K]

theorem exists_similitude (s : ℕ)
    (f : Points (splitQuadraticForm K (s+3))≃Points (splitQuadraticForm K (s+3)))
    (horth : ∀P R,ZeroOn (splitQuadraticForm K (s+3)).polarBilin (f P).val (f R).val ↔
      ZeroOn (splitQuadraticForm K (s+3)).polarBilin P.val R.val)
    (hlinear : ∀W : Subspaces (splitQuadraticForm K (s+3)),Module.finrank K W.val=s+3 →
      Nonempty (SemilinearPiece (splitQuadraticForm K (s+3)) f W (RingEquiv.refl K))) :
    ∃(c : K) (L : (Index (s+3)→K)≃ₗ[K](Index (s+3)→K)),c≠0 ∧
      (∀v,splitQuadraticForm K (s+3) (L v)=c*splitQuadraticForm K (s+3) v) ∧
      ∀R : Points (splitQuadraticForm K (s+3)),(f R).val=R.val.map L.toLinearMap := by
  let q := splitQuadraticForm K (s+3)
  let P := positiveSingular K (s+3)
  let Z := negativeSingular K (s+3)
  let F := Classical.choice (hlinear P (positiveSpace_finrank K (s+3)))
  let G := Classical.choice (hlinear Z (negativeSpace_finrank K (s+3)))
  obtain ⟨a,H,ha,hH,hHP,hHZ⟩ := exists_glued_similitude K (s+3) (by omega) f horth F G
  have hHi := CFSGQuadraticSimilitudeGeometry.inverse_quadratic q H a ha hH
  let f₀ := f.trans (CFSGQuadraticSimilitudeGeometry.pointEquiv q H.symm a⁻¹ (inv_ne_zero ha) hHi)
  have hlin₀ : ∀W : Subspaces q,Module.finrank K W.val=s+3 →
      Nonempty (SemilinearPiece q f₀ W (RingEquiv.refl K)) := by
    intro W hd
    exact ⟨CFSGQuadraticSimilitudeGeometry.postcomposePiece q H.symm a⁻¹ (inv_ne_zero ha) hHi
      f W (RingEquiv.refl K) (Classical.choice (hlinear W hd))⟩
  have hfix (W : Subspaces q) (A : SemilinearPiece q f W (RingEquiv.refl K))
      (hA : ∀x : W.val,H x.val=A.map x) :
      ∀R : Points q,R.val≤W.val → f₀ R=R := by
    intro R hR
    obtain ⟨v,hv,hv0⟩ := point_nonzero q R
    let x : W.val := ⟨v,hR hv⟩
    have hx0 : x≠0 := fun h=>hv0 (congrArg Subtype.val h)
    have hrep : ray q x.val (fun h=>hx0 (Subtype.ext h)) (W.property x.val x.property)=R :=
      Subtype.ext (point_span q R v hv hv0)
    have hF := (A.point x hx0).trans (congrArg (fun S : Points q=>(f S).val) hrep)
    change Submodule.span K {A.map x}=(f R).val at hF
    apply Subtype.ext
    change (f R).val.map H.symm.toLinearMap=R.val
    rw [←hF,Submodule.map_span,Set.image_singleton,←hA x]
    change Submodule.span K {H.symm (H x.val)}=R.val
    rw [H.symm_apply_apply]
    exact point_span q R v hv hv0
  obtain ⟨t,ht,hD⟩ := CFSGOrthogonalDNegativeDilation.exists_dilation K s f₀ hlin₀
    (hfix P F hHP) (hfix Z G hHZ)
  let D := CFSGOrthogonalDNegativeDilation.equiv K (s+3) t ht
  refine ⟨a*t,D.trans H,mul_ne_zero ha ht,?_,?_⟩
  · intro v
    change q (H (D v))=(a*t)*q v
    rw [hH]
    change a*q (CFSGOrthogonalDNegativeDilation.map K (s+3) t v)=(a*t)*q v
    rw [CFSGOrthogonalDNegativeDilation.map_quadratic,mul_assoc]
  · intro R
    obtain ⟨v,hv,hv0⟩ := point_nonzero q R
    have hz := R.property.2 v hv
    have hrep : ray q v hv0 hz=R := Subtype.ext (point_span q R v hv hv0)
    have h := hD v hv0 hz
    rw [hrep] at h
    change (f R).val.map H.symm.toLinearMap=
      Submodule.span K {CFSGOrthogonalDNegativeDilation.map K (s+3) t v} at h
    have he := (Submodule.map_symm_eq_iff H).mp h
    rw [Submodule.map_span,Set.image_singleton] at he
    rw [←point_span q R v hv hv0,Submodule.map_span,Set.image_singleton]
    exact he.symm

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDLinearPolarSimilitude
