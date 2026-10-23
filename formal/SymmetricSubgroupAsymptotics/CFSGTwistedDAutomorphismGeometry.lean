import SymmetricSubgroupAsymptotics.CFSGTwistedDLinearReconstruction
import SymmetricSubgroupAsymptotics.CFSGTwistedDGlobalFieldComponent
import SymmetricSubgroupAsymptotics.CFSGTwistedDFieldNormalization
import SymmetricSubgroupAsymptotics.CFSGQuadraticMaximalPieceRestriction

/-! Every actual automorphism of the original nonsplit D model has
a field-linear factorization on its actual singular points. The common
field component, all local pieces, and the global similitude are proved
internally. The conclusion supplies the geometric encoding for the
outer-order count; it does not assert that count. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTwistedDAutomorphismGeometry
open CFSGTwistedDFixedQuadraticSpace CFSGTwistedDGlobalFieldComponent
open CFSGTwistedDPointAction CFSGTwistedDPointOrthogonality CFSGTwistedDFieldNormalization
open CFSGTwistedDFieldGeometry CFSGTwistedDProjectiveUnipotent CFSGTwistedDPlaneFamilyAction
open CFSGTwistedDPointStars
open CFSGTwistedA2FixedField CFSGOrthogonalDIndexQuadraticSubspacePoints CFSGSingularPlaneTriangle

local instance (n : ℕ) (q : CFSG.PrimePower) :
    Module.Finite (fixedField q) (fixedSpace n q) := Module.Finite.of_finite
local instance (q : CFSG.PrimePower) (sigma : fixedField q ≃+* fixedField q) :
    RingHomSurjective sigma.toRingHom := ⟨sigma.surjective⟩
local instance (q : CFSG.PrimePower) (sigma : fixedField q ≃+* fixedField q) :
    RingHomInvPair sigma.toRingHom sigma.symm.toRingHom := RingHomInvPair.of_ringEquiv sigma
local instance (q : CFSG.PrimePower) (sigma : fixedField q ≃+* fixedField q) :
    RingHomInvPair sigma.symm.toRingHom sigma.toRingHom := RingHomInvPair.of_ringEquiv_symm sigma

theorem projective_exists_field_linear_factor (s : ℕ) (q : CFSG.PrimePower)
    (f : MulAut (Projective s q)) :
    ∃ (sigma : fixedField q ≃+* fixedField q) (t : fixedField q)
      (L : fixedSpace (s + 2) q ≃ₗ[fixedField q] fixedSpace (s + 2) q),
      t ≠ 0 ∧
      (∀ v, fixedQuadraticForm (s + 2) q (L v) = t * fixedQuadraticForm (s + 2) q v) ∧
      ∀ P : SingularPoints s q, (projectivePointActionHom s q f P).val =
        (P.val.map L.toLinearMap).map (vectorEquiv (s + 2) q sigma).toLinearMap := by
  let Q := fixedQuadraticForm (s + 2) q
  let pf := projectivePointActionHom s q f
  obtain ⟨sigma, hmax⟩ := exists_global_field_component s q f
  have hlinear : ∀ W : Subspaces Q,
      Nonempty (SemilinearPiece Q (normalizedPoints s q pf sigma) W (RingEquiv.refl (fixedField q))) := by
    intro W
    obtain ⟨F⟩ := CFSGQuadraticMaximalPieceRestriction.exists_piece_on_subspace Q pf sigma hmax W
    exact ⟨normalizedPiece s q pf W sigma F⟩
  have horth : ∀ P R, ZeroOn Q.polarBilin (normalizedPoints s q pf sigma P).val
      (normalizedPoints s q pf sigma R).val ↔ ZeroOn Q.polarBilin P.val R.val :=
    normalized_orthogonality s q pf (projectivePointAction_preserves_orthogonal s q f) sigma
  obtain ⟨t, L, ht, hL, hpoints⟩ := CFSGTwistedDLinearReconstruction.exists_linear_similitude
    (s + 2) q (by omega) (normalizedPoints s q pf sigma) horth hlinear
  refine ⟨sigma, t, L, ht, hL, ?_⟩
  intro P
  have he := hpoints P
  change (pf P).val.comap (vectorEquiv (s + 2) q sigma).toLinearMap = P.val.map L.toLinearMap at he
  rw [← he]
  exact (Submodule.map_comap_eq_of_surjective (vectorEquiv (s + 2) q sigma).surjective (pf P).val).symm

theorem original_exists_field_linear_factor (s : ℕ) (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.TwistedD (s + 4) q)]
    (f : MulAut (CFSG.Models.TwistedD (s + 4) q)) :
    ∃ (sigma : fixedField q ≃+* fixedField q) (t : fixedField q)
      (L : fixedSpace (s + 2) q ≃ₗ[fixedField q] fixedSpace (s + 2) q),
      t ≠ 0 ∧
      (∀ v, fixedQuadraticForm (s + 2) q (L v) = t * fixedQuadraticForm (s + 2) q v) ∧
      ∀ P : SingularPoints s q, (originalPointActionHom s q f P).val =
        (P.val.map L.toLinearMap).map (vectorEquiv (s + 2) q sigma).toLinearMap :=
  projective_exists_field_linear_factor s q
    (MulAut.congr (CFSGTwistedDRelativeProjectiveModel.originalRelativeProjectiveEquiv s q) f)

end SymmetricSubgroupAsymptotics.CFSGTwistedDAutomorphismGeometry
