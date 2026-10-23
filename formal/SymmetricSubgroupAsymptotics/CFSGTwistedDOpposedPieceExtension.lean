import SymmetricSubgroupAsymptotics.CFSGQuadraticOpposedCrossScalar
import SymmetricSubgroupAsymptotics.CFSGTwistedDHyperbolicCoordinates
import SymmetricSubgroupAsymptotics.CFSGTwistedDParameterSimilitudes

/-! After simultaneous alignment of opposed maximal singular spaces,
the two actual local linear representatives extend to one similitude
of the whole nonsplit space. A norm lift supplies the anisotropic-plane
multiplier. This is an extension of the given maps, not a split-space
replacement or a recognition assumption. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTwistedDOpposedPieceExtension
open CFSGTwistedDFixedQuadraticSpace CFSGTwistedDMaximalSingularDimension
open CFSGTwistedDNegativeSpaceCoordinates CFSGTwistedDHyperbolicCoordinates
open CFSGTwistedDParameterSimilitudes CFSGTwistedDRelativeNormScaling
open CFSGTwistedDRelativeTorusParameters CFSGTwistedDLinearParameters CFSGTwistedA2FixedField
open CFSGOrthogonalDIndexQuadraticSubspacePoints CFSGSingularPlaneTriangle

local instance (n : ℕ) (q : CFSG.PrimePower) :
    Module.Finite (fixedField q) (fixedSpace n q) := Module.Finite.of_finite

abbrev positiveSingular (n : ℕ) (q : CFSG.PrimePower) :
    Subspaces (fixedQuadraticForm n q) :=
  ⟨positiveSpace n q, (positiveSpace_maximal n q).1⟩

abbrev negativeSingular (n : ℕ) (q : CFSG.PrimePower) :
    Subspaces (fixedQuadraticForm n q) :=
  ⟨negativeSpace n q, negativeSpace_singular n q⟩

theorem recover_positive (n : ℕ) (q : CFSG.PrimePower)
    (v : fixedSpace n q) (hv : v ∈ positiveSpace n q) :
    positiveEmbedding n q (positivePart n q v) = v := by
  obtain ⟨x, rfl⟩ := hv
  rw [positivePart_positive]

theorem recover_negative (n : ℕ) (q : CFSG.PrimePower)
    (v : fixedSpace n q) (hv : v ∈ negativeSpace n q) :
    negativeEmbedding n q (negativePart n q v) = v := by
  obtain ⟨y, rfl⟩ := hv
  rw [negativePart_negative]

theorem positive_negative_disjoint (n : ℕ) (q : CFSG.PrimePower) :
    Disjoint (positiveSpace n q) (negativeSpace n q) := by
  apply Submodule.disjoint_def.mpr
  rintro v ⟨x, rfl⟩ ⟨y, he⟩
  have hx := congrArg (positivePart n q) he
  rw [positivePart_negative, positivePart_positive] at hx
  rw [← hx, map_zero]

theorem polar_embeddings (n : ℕ) (q : CFSG.PrimePower)
    (x y : Fin (n + 1) → fixedField q) :
    (fixedQuadraticForm n q).polarBilin (positiveEmbedding n q x) (negativeEmbedding n q y) =
      dotProduct x y := by
  rw [polar_negative, positivePart_positive]

def positivePieceMap (n : ℕ) (q : CFSG.PrimePower)
    (f : Points (fixedQuadraticForm n q) ≃ Points (fixedQuadraticForm n q))
    (F : SemilinearPiece (fixedQuadraticForm n q) f (positiveSingular n q)
      (RingEquiv.refl (fixedField q))) :
    (Fin (n + 1) → fixedField q) →ₗ[fixedField q] (Fin (n + 1) → fixedField q) :=
  (positivePart n q).comp (F.map.comp (positiveEmbedding n q).rangeRestrict)

def negativePieceMap (n : ℕ) (q : CFSG.PrimePower)
    (f : Points (fixedQuadraticForm n q) ≃ Points (fixedQuadraticForm n q))
    (G : SemilinearPiece (fixedQuadraticForm n q) f (negativeSingular n q)
      (RingEquiv.refl (fixedField q))) :
    (Fin (n + 1) → fixedField q) →ₗ[fixedField q] (Fin (n + 1) → fixedField q) :=
  (negativePart n q).comp (G.map.comp (negativeEmbedding n q).rangeRestrict)

theorem positivePieceMap_injective (n : ℕ) (q : CFSG.PrimePower)
    (f : Points (fixedQuadraticForm n q) ≃ Points (fixedQuadraticForm n q))
    (F : SemilinearPiece (fixedQuadraticForm n q) f (positiveSingular n q)
      (RingEquiv.refl (fixedField q)))
    (hF : ∀ x, F.map x ∈ positiveSpace n q) : Function.Injective (positivePieceMap n q f F) := by
  intro x y he
  apply positiveEmbedding_injective n q
  have h := congrArg (positiveEmbedding n q) he
  change positiveEmbedding n q (positivePart n q (F.map _)) =
    positiveEmbedding n q (positivePart n q (F.map _)) at h
  rw [recover_positive n q _ (hF _), recover_positive n q _ (hF _)] at h
  exact congrArg Subtype.val (F.injective h)

theorem negativePieceMap_injective (n : ℕ) (q : CFSG.PrimePower)
    (f : Points (fixedQuadraticForm n q) ≃ Points (fixedQuadraticForm n q))
    (G : SemilinearPiece (fixedQuadraticForm n q) f (negativeSingular n q)
      (RingEquiv.refl (fixedField q)))
    (hG : ∀ y, G.map y ∈ negativeSpace n q) : Function.Injective (negativePieceMap n q f G) := by
  intro x y he
  apply negativeEmbedding_injective n q
  have h := congrArg (negativeEmbedding n q) he
  change negativeEmbedding n q (negativePart n q (G.map _)) =
    negativeEmbedding n q (negativePart n q (G.map _)) at h
  rw [recover_negative n q _ (hG _), recover_negative n q _ (hG _)] at h
  exact congrArg Subtype.val (G.injective h)

theorem exists_extension (n : ℕ) (q : CFSG.PrimePower)
    (f : Points (fixedQuadraticForm n q) ≃ Points (fixedQuadraticForm n q))
    (horth : ∀ R S, ZeroOn (fixedQuadraticForm n q).polarBilin (f R).val (f S).val ↔
      ZeroOn (fixedQuadraticForm n q).polarBilin R.val S.val)
    (F : SemilinearPiece (fixedQuadraticForm n q) f (positiveSingular n q)
      (RingEquiv.refl (fixedField q)))
    (G : SemilinearPiece (fixedQuadraticForm n q) f (negativeSingular n q)
      (RingEquiv.refl (fixedField q)))
    (hF : ∀ x, F.map x ∈ positiveSpace n q) (hG : ∀ y, G.map y ∈ negativeSpace n q) :
    ∃ (t : fixedField q) (L : fixedSpace n q ≃ₗ[fixedField q] fixedSpace n q), t ≠ 0 ∧
      (∀ v, fixedQuadraticForm n q (L v) = t * fixedQuadraticForm n q v) ∧
      (∀ x, L (positiveEmbedding n q x) = F.map ((positiveEmbedding n q).rangeRestrict x)) ∧
      (∀ y, L (negativeEmbedding n q y) = G.map ((negativeEmbedding n q).rangeRestrict y)) := by
  have hPne : positiveSpace n q ≠ ⊥ := Submodule.one_le_finrank_iff.mp (by
    rw [positiveSpace_finrank]
    omega)
  obtain ⟨t, ht, hcross⟩ := CFSGQuadraticOpposedCrossScalar.exists_cross_scalar
    (fixedQuadraticForm n q) (positiveSpace n q) (negativeSpace n q)
    (positiveSpace_maximal n q) (negativeSpace_maximal n q)
    (positive_negative_disjoint n q) hPne f horth F G
  obtain ⟨c, hc⟩ := normHom_surjective q (Units.mk0 t ht)
  let A := LinearEquiv.ofInjectiveEndo (positivePieceMap n q f F)
    (positivePieceMap_injective n q f F hF)
  let B := LinearEquiv.ofInjectiveEndo (negativePieceMap n q f G)
    (negativePieceMap_injective n q f G hG)
  have hA (x) : positiveEmbedding n q (A x) = F.map ((positiveEmbedding n q).rangeRestrict x) :=
    recover_positive n q _ (hF _)
  have hB (y) : negativeEmbedding n q (B y) = G.map ((negativeEmbedding n q).rangeRestrict y) :=
    recover_negative n q _ (hG _)
  have hscalar : (normHom q c : fixedField q) = t := congrArg (fun z : (fixedField q)ˣ => (z : fixedField q)) hc
  have hdot (x y) : dotProduct (A x) (B y) = (normHom q c : fixedField q) * dotProduct x y := by
    have he := hcross ((positiveEmbedding n q).rangeRestrict x) ((negativeEmbedding n q).rangeRestrict y)
    rw [← hA x, ← hB y, polar_embeddings] at he
    change dotProduct (A x) (B y) = t *
      (fixedQuadraticForm n q).polarBilin (positiveEmbedding n q x) (negativeEmbedding n q y) at he
    rw [polar_embeddings] at he
    rw [hscalar]
    exact he
  refine ⟨t, parameterChange n q A B c, ht, ?_, ?_, ?_⟩
  · intro v
    rw [parameterChange_quadratic n q A B c hdot v, hscalar]
  · intro x
    rw [← hA]
    apply (linearParameters n q).injective
    rw [parameterChange_coordinates, parameters_positive, parameters_positive]
    simp only [map_zero, mul_zero]
  · intro y
    rw [← hB]
    apply (linearParameters n q).injective
    rw [parameterChange_coordinates, parameters_negative, parameters_negative]
    simp only [map_zero, mul_zero]

end SymmetricSubgroupAsymptotics.CFSGTwistedDOpposedPieceExtension
