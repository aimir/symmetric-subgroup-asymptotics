import SymmetricSubgroupAsymptotics.CFSGTwistedDProjectivePlaneLabel

/-! Scalar extension of the actual fixed-field displacement image.
The fixed space spans the natural extension-field carrier, so its
displacement image spans the SAME ambient displacement image. These
are exact span equalities, not an implicit identification of planes. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGTwistedDDisplacementScalarSpan
open CFSGOrthogonalDSerreMatrices CFSGTwistedDRelativeElementaryGroup
open CFSGTwistedDFixedQuadraticSpace CFSGTwistedDFixedQuadraticAction
open CFSGTwistedDFixedQuadraticNondegenerate CFSGLinearConjugateDisplacement
open CFSGTwistedDPlaneRootLine CFSGTwistedDRootPlaneImage CFSGTwistedDSingularPlaneOrbit
open CFSGTwistedDProjectivePlaneLabel CFSGTwistedDRelativeUnipotentSylow CFSGTwistedA2FixedField

def scalarSpan (n : ℕ) (q : CFSG.PrimePower)
    (P : Submodule (fixedField q) (fixedSpace n q)) :
    Submodule (q.Extension 2) (Index (n + 2) → q.Extension 2) :=
  Submodule.span (q.Extension 2) ((fun x : fixedSpace n q => x.val) '' (P : Set (fixedSpace n q)))

theorem displacement_coe (n : ℕ) (q : CFSG.PrimePower)
    (g : relativeRootGroup n q) (v : fixedSpace n q) :
    (displacement (fixedLinearHom n q) g v).val =
      Matrix.mulVecLin ((g.val : Mat (q.Extension 2) (n + 2)) - 1) v.val := by
  change (fixedLinearHom n q g v).val - v.val =
    ((g.val : Mat (q.Extension 2) (n + 2)) - 1) *ᵥ v.val
  rw [fixedLinearHom_apply, Matrix.sub_mulVec, Matrix.one_mulVec]

theorem displacement_scalarSpan (n : ℕ) (q : CFSG.PrimePower)
    (g : relativeRootGroup n q) :
    scalarSpan n q (LinearMap.range (displacement (fixedLinearHom n q) g)) =
      LinearMap.range (Matrix.mulVecLin ((g.val : Mat (q.Extension 2) (n + 2)) - 1)) := by
  let D := Matrix.mulVecLin ((g.val : Mat (q.Extension 2) (n + 2)) - 1)
  have he : (fun x : fixedSpace n q => x.val) ''
        (LinearMap.range (displacement (fixedLinearHom n q) g) : Set (fixedSpace n q)) =
      D '' Set.range (fun x : fixedSpace n q => x.val) := by
    ext x
    constructor
    · rintro ⟨y, ⟨v, rfl⟩, rfl⟩
      exact ⟨v.val, ⟨v, rfl⟩, (displacement_coe n q g v).symm⟩
    · rintro ⟨y, ⟨v, rfl⟩, rfl⟩
      exact ⟨displacement (fixedLinearHom n q) g v, ⟨v, rfl⟩, displacement_coe n q g v⟩
  unfold scalarSpan
  rw [he, ← Submodule.map_span, fixedSpace_span, ← LinearMap.range_eq_map]

theorem conjugateRootPlane_scalarSpan (s : ℕ) (q : CFSG.PrimePower)
    (g : relativeRootGroup (s + 2) q) :
    scalarSpan (s + 2) q (conjugateRootPlane s q g) =
      CFSGOrthogonalDIndexPlaneRootLine.conjugateRootPlane (q.Extension 2) s
        (relativeInclusion s q g) := by
  rw [← conjugate_displacement_range s q g 1 one_ne_zero, displacement_scalarSpan]
  have he := CFSGOrthogonalDIndexRootPlaneImage.conjugate_highestRoot_displacement_range
    (q.Extension 2) s (relativeInclusion s q g) (1 : q.Extension 2) one_ne_zero
  change LinearMap.range (Matrix.mulVecLin
      (((relativeInclusion s q g * CFSGOrthogonalDIndexPairOperator.highestRoot
          (q.Extension 2) s ((1 : fixedField q) : q.Extension 2) *
        (relativeInclusion s q g)⁻¹).val : Mat (q.Extension 2) (s + 4)) - 1)) = _ at he
  rw [← inclusion_conjugate_highest s q g (1 : fixedField q)] at he
  exact he

end SymmetricSubgroupAsymptotics.CFSGTwistedDDisplacementScalarSpan
