import SymmetricSubgroupAsymptotics.CFSGTwistedDZeroHyperbolicKernel
import SymmetricSubgroupAsymptotics.CFSGTwistedDZeroAnisotropicDilation
import SymmetricSubgroupAsymptotics.CFSGQuadraticSimilitudeNormalization

/-! With both opposed halves fixed pointwise, the common mixed ratio
and the actual anisotropic kernel reconstruct the entire point map.
Both normalizing maps are genuine similitudes of the original nonsplit
space. No full-hyperbolic-fixation hypothesis remains in the result. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTwistedDHalfFixedReconstruction
open CFSGTwistedDFixedQuadraticSpace CFSGTwistedDMaximalSingularDimension
open CFSGTwistedDNegativeSpaceCoordinates CFSGTwistedDHyperbolicCoordinates
open CFSGTwistedA2FixedField CFSGOrthogonalDIndexQuadraticSubspacePoints CFSGSingularPlaneTriangle
open CFSGQuadraticSimilitudeGeometry CFSGQuadraticSimilitudeNormalization

local instance (n : ℕ) (q : CFSG.PrimePower) :
    Module.Finite (fixedField q) (fixedSpace n q) := Module.Finite.of_finite

theorem exists_linear_similitude (n : ℕ) (q : CFSG.PrimePower) (hn : 2 ≤ n)
    (f : Points (fixedQuadraticForm n q) ≃ Points (fixedQuadraticForm n q))
    (horth : ∀ P R, ZeroOn (fixedQuadraticForm n q).polarBilin (f P).val (f R).val ↔
      ZeroOn (fixedQuadraticForm n q).polarBilin P.val R.val)
    (hlinear : ∀ W : Subspaces (fixedQuadraticForm n q),
      Nonempty (SemilinearPiece (fixedQuadraticForm n q) f W (RingEquiv.refl (fixedField q))))
    (hfixP : ∀ P : Points (fixedQuadraticForm n q), P.val ≤ positiveSpace n q → f P = P)
    (hfixZ : ∀ P : Points (fixedQuadraticForm n q), P.val ≤ negativeSpace n q → f P = P) :
    ∃ (t : fixedField q) (L : fixedSpace n q ≃ₗ[fixedField q] fixedSpace n q), t ≠ 0 ∧
      (∀ v, fixedQuadraticForm n q (L v) = t * fixedQuadraticForm n q v) ∧
      ∀ P : Points (fixedQuadraticForm n q), (f P).val = P.val.map L.toLinearMap := by
  obtain ⟨t, D, ht, hD, hray⟩ :=
    CFSGTwistedDZeroAnisotropicDilation.exists_dilation n q hn f hlinear hfixP hfixZ
  let Q := fixedQuadraticForm n q
  let invD := pointEquiv Q D.symm t⁻¹ (inv_ne_zero ht) (inverse_quadratic Q D t ht hD)
  let g := f.trans invD
  have hgorth : ∀ P R, ZeroOn Q.polarBilin (g P).val (g R).val ↔
      ZeroOn Q.polarBilin P.val R.val :=
    postcompose_orthogonality Q D.symm t⁻¹ (inv_ne_zero ht)
      (inverse_quadratic Q D t ht hD) f horth
  have hglinear : ∀ W : Subspaces Q,
      Nonempty (SemilinearPiece Q g W (RingEquiv.refl (fixedField q))) := by
    intro W
    obtain ⟨F⟩ := hlinear W
    exact ⟨postcomposePiece Q D.symm t⁻¹ (inv_ne_zero ht)
      (inverse_quadratic Q D t ht hD) f W (RingEquiv.refl (fixedField q)) F⟩
  have hgfix : ∀ P : Points Q, (∀ v ∈ P.val, anisotropicPart n q v = 0) → g P = P := by
    intro P hP
    obtain ⟨v, hv, hv0⟩ := point_nonzero Q P
    have hvQ := P.property.2 v hv
    have hPr : ray Q v hv0 hvQ = P := Subtype.ext (point_span Q P v hv hv0)
    have he := hray v hv0 hvQ (hP v hv)
    rw [hPr] at he
    apply Subtype.ext
    change (f P).val.map D.symm.toLinearMap = P.val
    rw [he, Submodule.map_span, Set.image_singleton]
    change Submodule.span (fixedField q) {D.symm (D v)} = P.val
    rw [D.symm_apply_apply]
    exact point_span Q P v hv hv0
  obtain ⟨K, hK, hpoints⟩ := CFSGTwistedDZeroHyperbolicKernel.exists_linear_isometry
    n q (by omega) g hgorth hgfix hglinear
  refine ⟨t, K.trans D, ht, ?_, ?_⟩
  · intro v
    change Q (D (K v)) = t * Q v
    rw [hD, hK]
  · intro P
    have he := congrArg (fun S : Submodule (fixedField q) (fixedSpace n q) =>
      S.map D.toLinearMap) (hpoints P)
    change ((f P).val.map D.symm.toLinearMap).map D.toLinearMap =
      (P.val.map K.toLinearMap).map D.toLinearMap at he
    rw [← Submodule.map_comp] at he
    have hid : D.toLinearMap.comp D.symm.toLinearMap = LinearMap.id := by
      apply LinearMap.ext
      intro v
      exact D.apply_symm_apply v
    rw [hid, Submodule.map_id] at he
    rw [← Submodule.map_comp] at he
    exact he

end SymmetricSubgroupAsymptotics.CFSGTwistedDHalfFixedReconstruction
