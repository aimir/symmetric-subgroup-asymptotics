import SymmetricSubgroupAsymptotics.CFSGQuadraticPieceRanges
import SymmetricSubgroupAsymptotics.CFSGQuadraticSimilitudeGeometry
import SymmetricSubgroupAsymptotics.CFSGTwistedDOpposedPieceExtension
import SymmetricSubgroupAsymptotics.CFSGTwistedDOpposedPairAlignment

/-! The ranges of the two actual local pieces are simultaneously
aligned by ONE literal relative-root word. Postcomposition retains their
exact point equations and puts their images in the standard positive
and negative spaces. No independent alignment choices are identified. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTwistedDOpposedPieceAlignment
open CFSGTwistedDFixedQuadraticSpace CFSGTwistedDFixedQuadraticAction
open CFSGTwistedDRelativeElementaryGroup CFSGTwistedDOpposedPieceExtension
open CFSGTwistedDMaximalSingularDimension CFSGTwistedDNegativeSpaceCoordinates CFSGTwistedA2FixedField
open CFSGOrthogonalDIndexQuadraticSubspacePoints CFSGQuadraticSimilitudeGeometry

local instance (n : ℕ) (q : CFSG.PrimePower) :
    Module.Finite (fixedField q) (fixedSpace n q) := Module.Finite.of_finite

local instance (q : CFSG.PrimePower) :
    RingHomSurjective (RingEquiv.refl (fixedField q)).toRingHom :=
  ⟨fun x => ⟨x, rfl⟩⟩

theorem root_quadratic (n : ℕ) (q : CFSG.PrimePower) (g : relativeRootGroup n q)
    (v : fixedSpace n q) :
    fixedQuadraticForm n q (fixedLinearHom n q g v) = (1 : fixedField q) * fixedQuadraticForm n q v :=
  (fixedLinearHom_preserves_Q n q g v).trans (one_mul _).symm

def rootPointEquiv (n : ℕ) (q : CFSG.PrimePower) (g : relativeRootGroup n q) :
    Points (fixedQuadraticForm n q) ≃ Points (fixedQuadraticForm n q) :=
  pointEquiv (fixedQuadraticForm n q) (fixedLinearHom n q g) 1 one_ne_zero
    (root_quadratic n q g)

theorem rootPointEquiv_val (n : ℕ) (q : CFSG.PrimePower) (g : relativeRootGroup n q)
    (P : Points (fixedQuadraticForm n q)) :
    (rootPointEquiv n q g P).val = P.val.map (fixedLinearHom n q g).toLinearMap := rfl

def alignedPiece (n : ℕ) (q : CFSG.PrimePower) (g : relativeRootGroup n q)
    (f : Points (fixedQuadraticForm n q) ≃ Points (fixedQuadraticForm n q))
    (W : Subspaces (fixedQuadraticForm n q))
    (F : SemilinearPiece (fixedQuadraticForm n q) f W (RingEquiv.refl (fixedField q))) :
    SemilinearPiece (fixedQuadraticForm n q) (f.trans (rootPointEquiv n q g)) W
      (RingEquiv.refl (fixedField q)) :=
  postcomposePiece (fixedQuadraticForm n q) (fixedLinearHom n q g) 1 one_ne_zero
    (root_quadratic n q g) f W (RingEquiv.refl (fixedField q)) F

theorem alignedPiece_apply (n : ℕ) (q : CFSG.PrimePower) (g : relativeRootGroup n q)
    (f : Points (fixedQuadraticForm n q) ≃ Points (fixedQuadraticForm n q))
    (W : Subspaces (fixedQuadraticForm n q))
    (F : SemilinearPiece (fixedQuadraticForm n q) f W (RingEquiv.refl (fixedField q)))
    (x : W.val) : (alignedPiece n q g f W F).map x = fixedLinearHom n q g (F.map x) := rfl

theorem exists_align_pieces (n : ℕ) (q : CFSG.PrimePower)
    (f : Points (fixedQuadraticForm n q) ≃ Points (fixedQuadraticForm n q))
    (F : SemilinearPiece (fixedQuadraticForm n q) f (positiveSingular n q)
      (RingEquiv.refl (fixedField q)))
    (G : SemilinearPiece (fixedQuadraticForm n q) f (negativeSingular n q)
      (RingEquiv.refl (fixedField q))) :
    ∃ g : relativeRootGroup n q,
      (∀ x, (alignedPiece n q g f (positiveSingular n q) F).map x ∈ positiveSpace n q) ∧
      (∀ y, (alignedPiece n q g f (negativeSingular n q) G).map y ∈ negativeSpace n q) := by
  have hF := CFSGQuadraticPieceRanges.range_maximal (fixedQuadraticForm n q) f
    (positiveSingular n q) (positiveSpace_maximal n q) F
  have hG := CFSGQuadraticPieceRanges.range_maximal (fixedQuadraticForm n q) f
    (negativeSingular n q) (negativeSpace_maximal n q) G
  have hFG := CFSGQuadraticPieceRanges.ranges_disjoint (fixedQuadraticForm n q) f
    (positiveSingular n q) (negativeSingular n q) (positive_negative_disjoint n q) F G
  obtain ⟨g, hgF, hgG⟩ := CFSGTwistedDOpposedPairAlignment.exists_align_maximal n q
    F.map.range G.map.range hF hG hFG
  refine ⟨g, ?_, ?_⟩
  · intro x
    rw [alignedPiece_apply, ← hgF]
    exact ⟨F.map x, ⟨x, rfl⟩, rfl⟩
  · intro y
    rw [alignedPiece_apply, ← hgG]
    exact ⟨G.map y, ⟨y, rfl⟩, rfl⟩

end SymmetricSubgroupAsymptotics.CFSGTwistedDOpposedPieceAlignment
