import SymmetricSubgroupAsymptotics.CFSGOrthogonalBLinearGeometryNormalization
import SymmetricSubgroupAsymptotics.CFSGOrthogonalBZeroMiddleDilation
import SymmetricSubgroupAsymptotics.CFSGOrthogonalBDilationRatioSquare
import SymmetricSubgroupAsymptotics.CFSGOrthogonalBSquareDilationRealization
import SymmetricSubgroupAsymptotics.CFSGOrthogonalBMiddleFlipSpecial

/-! Whole-space realization for the SAME original B polar point map.
Actual field-normalized linear pieces, opposed-space normalization,
uniform mixed-scalar coherence, the proved square obstruction, and the
actual zero-middle kernel together yield a literal determinant-one
isometry. No whole-polar recognition premise remains in this theorem. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalBLinearPolarIsometry
open CFSGOrthogonalBSerreMatrices CFSGOrthogonalBPositiveSubspace
open CFSGOrthogonalBOpposedGraphShear CFSGOrthogonalBSpecialFormGroup
open CFSGOrthogonalBLinearGeometryNormalization CFSGOrthogonalBDilationRatioSquare
open CFSGOrthogonalBSquareDilationRealization CFSGPolarSubspacePoints CFSGSingularPlaneTriangle
variable (K : Type) [Field K] [Finite K]

theorem exists_special_isometry_of_linear_pieces (p : ℕ) [Fact p.Prime] [CharP K p]
    (h2 : (2 : K)≠0) (s : ℕ)
    (f : Points (gram K (s+3)).toBilin'≃Points (gram K (s+3)).toBilin')
    (l : Planes (gram K (s+3)).toBilin'≃Planes (gram K (s+3)).toBilin')
    (hinc : ∀P L,(f P).val≤(l L).val ↔ P.val≤L.val)
    (horth : ∀P Q,ZeroOn (gram K (s+3)).toBilin' (f P).val (f Q).val ↔
      ZeroOn (gram K (s+3)).toBilin' P.val Q.val)
    (hlinear : ∀W : Subspaces (gram K (s+3)).toBilin',Module.finrank K W.val=s+3 →
      Nonempty (SemilinearPiece (gram K (s+3)).toBilin' f W (RingEquiv.refl K))) :
    ∃g : specialFormUnits K (s+3),f=CFSGOrthogonalBSpecialGeometry.point K (s+3) g := by
  let B := (gram K (s+3)).toBilin'
  let φ := CFSGOrthogonalBSpecialGeometry.pointAction K (s+3)
  obtain ⟨a,hfixP,hfixZ⟩ := exists_opposed_point_normalization K p h2 s f l hinc horth hlinear
  let f1 := f.trans (φ a)
  have horth1 : ∀P Q : Points B,ZeroOn B (f1 P).val (f1 Q).val ↔ ZeroOn B P.val Q.val :=
    fun P Q=>(CFSGOrthogonalBSpecialGeometry.orthogonality K (s+3) a (f P) (f Q)).trans (horth P Q)
  have hlinear1 : ∀W : Subspaces B,Module.finrank K W.val=s+3 →
      Nonempty (SemilinearPiece B f1 W (RingEquiv.refl K)) := by
    intro W hd
    exact ⟨CFSGPolarIsometryGeometry.postcomposePiece B
      (CFSGOrthogonalBSpecialGeometry.linearEquiv K (s+3) a)
      (CFSGOrthogonalBSpecialGeometry.pairing K (s+3) a) f W (RingEquiv.refl K)
      (Classical.choice (hlinear W hd))⟩
  obtain ⟨t,ht,hratio⟩ := CFSGOrthogonalBZeroMiddleDilation.exists_dilation K h2 s f1 hlinear1 hfixP hfixZ
  obtain ⟨g,hg⟩ := exists_special_square_ratio K (s+3) t
    (ratio_is_nonzero_square K h2 s f1 horth1 hfixP hfixZ t ht hratio)
  let f2 := f1.trans (φ g⁻¹)
  have horth2 : ∀P Q : Points B,ZeroOn B (f2 P).val (f2 Q).val ↔ ZeroOn B P.val Q.val :=
    fun P Q=>(CFSGOrthogonalBSpecialGeometry.orthogonality K (s+3) g⁻¹ (f1 P) (f1 Q)).trans (horth1 P Q)
  have hzero : ∀R : Points B,(∀v∈R.val,v (middle (s+3))=0) → f2 R=R := by
    intro R hm
    obtain ⟨v,hv,hv0⟩ := point_nonzero B R
    have hvn : B v v=0 := R.property.2 v hv v hv
    have hr : ray B v hv0 hvn=R := Subtype.ext (point_span B R v hv hv0)
    have hR : (f1 R).val=R.val.map (g.val : Mat K (s+3)).mulVecLin := by
      have he := hratio v hv0 hvn (hm v hv)
      rw [hr] at he
      calc
        _ = Submodule.span K {CFSGOrthogonalBNegativeDilation.map K (s+3) t v} := he
        _ = (Submodule.span K {v}).map (CFSGOrthogonalBNegativeDilation.map K (s+3) t) := by
          rw [Submodule.map_span,Set.image_singleton]
        _ = R.val.map (CFSGOrthogonalBNegativeDilation.map K (s+3) t) := by rw [point_span B R v hv hv0]
        _ = _ := hg R.val hm
    apply Subtype.ext
    change (f1 R).val.map (((g.val⁻¹ : (Mat K (s+3))ˣ) : Mat K (s+3))).mulVecLin=R.val
    rw [hR,←CFSGMatrixSubspaceUnitAction.map_mul,inv_mul_cancel,Units.val_one,
      Matrix.mulVecLin_one,Submodule.map_id]
  obtain ⟨c,hc⟩ := CFSGOrthogonalBMiddleFlipSpecial.zero_middle_kernel_is_special_action
    K h2 s f2 horth2 (fun R hR=>hzero R hR)
  have he2 : f2=φ c := by
    apply Equiv.ext
    intro P
    exact Subtype.ext (hc P)
  have hegroup : φ g⁻¹*(φ a*f)=φ c := by
    apply Equiv.ext
    intro P
    exact congrArg (fun e : Equiv.Perm (Points B)=>e P) he2
  refine ⟨a⁻¹*g*c,?_⟩
  change f=φ (a⁻¹*g*c)
  calc
    f = (φ a)⁻¹*(φ g*(φ g⁻¹*(φ a*f))) := by simp [map_inv,mul_assoc]
    _ = (φ a)⁻¹*(φ g*φ c) := by rw [hegroup]
    _ = φ (a⁻¹*g*c) := by simp only [map_mul,map_inv,mul_assoc]

end SymmetricSubgroupAsymptotics.CFSGOrthogonalBLinearPolarIsometry
