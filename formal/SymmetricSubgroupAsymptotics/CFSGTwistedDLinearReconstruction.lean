import SymmetricSubgroupAsymptotics.CFSGTwistedDHalfFixedReconstruction
import SymmetricSubgroupAsymptotics.CFSGTwistedDOpposedPieceAlignment

/-! Global linear reconstruction on the original nonsplit quadratic
space. Arbitrary local-piece ranges are aligned by one actual root
word; their exact extension removes both half actions. The common
ratio and anisotropic kernel then remove the remaining point action.
No pointwise-fixation or ambient-realization premise is assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTwistedDLinearReconstruction
open CFSGTwistedDFixedQuadraticSpace CFSGTwistedDFixedQuadraticAction
open CFSGTwistedDMaximalSingularDimension CFSGTwistedDNegativeSpaceCoordinates
open CFSGTwistedDOpposedPieceExtension CFSGTwistedDOpposedPieceAlignment CFSGTwistedA2FixedField
open CFSGOrthogonalDIndexQuadraticSubspacePoints CFSGSingularPlaneTriangle
open CFSGQuadraticSimilitudeGeometry CFSGQuadraticSimilitudeNormalization

local instance (n : ℕ) (q : CFSG.PrimePower) :
    Module.Finite (fixedField q) (fixedSpace n q) := Module.Finite.of_finite

private theorem undo_linear_map {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (L : V ≃ₗ[K] V) (S T : Submodule K V) (h : S.map L.toLinearMap = T) :
    S = T.map L.symm.toLinearMap := by
  have he := congrArg (fun U : Submodule K V => U.map L.symm.toLinearMap) h
  dsimp only at he
  rw [← Submodule.map_comp] at he
  have hi : L.symm.toLinearMap.comp L.toLinearMap = LinearMap.id := by
    apply LinearMap.ext
    intro v
    exact L.symm_apply_apply v
  rw [hi, Submodule.map_id] at he
  exact he

theorem exists_linear_similitude (n : ℕ) (q : CFSG.PrimePower) (hn : 2 ≤ n)
    (f : Points (fixedQuadraticForm n q) ≃ Points (fixedQuadraticForm n q))
    (horth : ∀ P R, ZeroOn (fixedQuadraticForm n q).polarBilin (f P).val (f R).val ↔
      ZeroOn (fixedQuadraticForm n q).polarBilin P.val R.val)
    (hlinear : ∀ W : Subspaces (fixedQuadraticForm n q),
      Nonempty (SemilinearPiece (fixedQuadraticForm n q) f W (RingEquiv.refl (fixedField q)))) :
    ∃ (t : fixedField q) (L : fixedSpace n q ≃ₗ[fixedField q] fixedSpace n q), t ≠ 0 ∧
      (∀ v, fixedQuadraticForm n q (L v) = t * fixedQuadraticForm n q v) ∧
      ∀ P : Points (fixedQuadraticForm n q), (f P).val = P.val.map L.toLinearMap := by
  let Q := fixedQuadraticForm n q
  obtain ⟨F⟩ := hlinear (positiveSingular n q)
  obtain ⟨G⟩ := hlinear (negativeSingular n q)
  obtain ⟨g, hF, hG⟩ := exists_align_pieces n q f F G
  let A := fixedLinearHom n q g
  let f₁ := f.trans (rootPointEquiv n q g)
  let F₁ := alignedPiece n q g f (positiveSingular n q) F
  let G₁ := alignedPiece n q g f (negativeSingular n q) G
  have horth₁ : ∀ P R, ZeroOn Q.polarBilin (f₁ P).val (f₁ R).val ↔
      ZeroOn Q.polarBilin P.val R.val :=
    postcompose_orthogonality Q A 1 one_ne_zero (root_quadratic n q g) f horth
  have hlinear₁ : ∀ W : Subspaces Q,
      Nonempty (SemilinearPiece Q f₁ W (RingEquiv.refl (fixedField q))) := by
    intro W
    obtain ⟨H⟩ := hlinear W
    exact ⟨alignedPiece n q g f W H⟩
  obtain ⟨t₁, D, ht₁, hD, hDP, hDZ⟩ := exists_extension n q f₁ horth₁ F₁ G₁ hF hG
  let f₂ := f₁.trans (pointEquiv Q D.symm t₁⁻¹ (inv_ne_zero ht₁)
    (inverse_quadratic Q D t₁ ht₁ hD))
  have horth₂ : ∀ P R, ZeroOn Q.polarBilin (f₂ P).val (f₂ R).val ↔
      ZeroOn Q.polarBilin P.val R.val :=
    postcompose_orthogonality Q D.symm t₁⁻¹ (inv_ne_zero ht₁)
      (inverse_quadratic Q D t₁ ht₁ hD) f₁ horth₁
  have hlinear₂ : ∀ W : Subspaces Q,
      Nonempty (SemilinearPiece Q f₂ W (RingEquiv.refl (fixedField q))) := by
    intro W
    obtain ⟨H⟩ := hlinear₁ W
    exact ⟨postcomposePiece Q D.symm t₁⁻¹ (inv_ne_zero ht₁)
      (inverse_quadratic Q D t₁ ht₁ hD) f₁ W (RingEquiv.refl (fixedField q)) H⟩
  have hextP : ∀ x : (positiveSpace n q), D x.val = F₁.map x := by
    rintro ⟨v, ⟨u, rfl⟩⟩
    exact hDP u
  have hextZ : ∀ y : (negativeSpace n q), D y.val = G₁.map y := by
    rintro ⟨v, ⟨u, rfl⟩⟩
    exact hDZ u
  have hfixP : ∀ P : Points Q, P.val ≤ positiveSpace n q → f₂ P = P :=
    inverse_extension_fixes_points Q D t₁ ht₁ hD f₁ (positiveSingular n q) F₁ hextP
  have hfixZ : ∀ P : Points Q, P.val ≤ negativeSpace n q → f₂ P = P :=
    inverse_extension_fixes_points Q D t₁ ht₁ hD f₁ (negativeSingular n q) G₁ hextZ
  obtain ⟨t₂, K, ht₂, hK, hpoints⟩ :=
    CFSGTwistedDHalfFixedReconstruction.exists_linear_similitude n q hn f₂ horth₂ hlinear₂ hfixP hfixZ
  let L := (K.trans D).trans A.symm
  refine ⟨t₁ * t₂, L, mul_ne_zero ht₁ ht₂, ?_, ?_⟩
  · intro v
    have hAinv : ∀ w, Q (A.symm w) = Q w := by
      intro w
      have he := root_quadratic n q g (A.symm w)
      change Q (A (A.symm w)) = 1 * Q (A.symm w) at he
      rw [A.apply_symm_apply, one_mul] at he
      exact he.symm
    change Q (A.symm (D (K v))) = (t₁ * t₂) * Q v
    rw [hAinv, hD, hK, mul_assoc]
  · intro P
    have h₂ : (f₁ P).val.map D.symm.toLinearMap = P.val.map K.toLinearMap := hpoints P
    have h₁ := undo_linear_map D.symm (f₁ P).val (P.val.map K.toLinearMap) h₂
    change (f P).val.map A.toLinearMap =
      (P.val.map K.toLinearMap).map D.toLinearMap at h₁
    have he := undo_linear_map A (f P).val
      ((P.val.map K.toLinearMap).map D.toLinearMap) h₁
    rw [← Submodule.map_comp, ← Submodule.map_comp] at he
    exact he

end SymmetricSubgroupAsymptotics.CFSGTwistedDLinearReconstruction
