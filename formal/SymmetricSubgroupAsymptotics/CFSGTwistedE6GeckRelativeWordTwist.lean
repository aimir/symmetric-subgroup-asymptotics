import SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckRootSubgroupTwist
import SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckOriginalRootSections
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckOrthogonalWeyl

/-! The relative-word MATRIX conjugators are literally twist fixed.
This is proved directly by orthogonal simple Weyl commutation; it is not
inferred from fixed original actions through a possibly central kernel. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckRelativeWordTwist
open CFSGTwistedE6GeckRootSubgroupTwist CFSGTwistedE6GeckMatrixTwist
open CFSGTwistedE6GeckDiagramCovariance CFSGTwistedE6GeckSourceWordAction
open CFSGTwistedE6GeckSourceAction CFSGTwistedE6GeckOriginalRootSections
open CFSGTwistedE6RelativeWeylOrbits CFSGTwistedE6FixedWordClassification
open CFSGExceptionalNormTwoBases CFSGExceptionalCartanPositiveDefinite
open CFSGNormTwoGeckOrthogonalWeyl CFSGSerreQuadraticMatrix CFSGSerreQuadraticWeylWord

theorem orbit_word_fixed (K : Type) [CommRing K] (sigma : K≃+*K) (a : Fin 4) :
    unitTwist K sigma (canonicalWord rawData K (orbitWord a))=canonicalWord rawData K (orbitWord a) := by
  rw [unitTwist_word]
  fin_cases a
  · change canonicalWeyl rawData K 5*(canonicalWeyl rawData K 0*1)=
      canonicalWeyl rawData K 0*(canonicalWeyl rawData K 5*1)
    simpa only [mul_one] using
      (orthogonal_weyls CartanMatrix.E₆ CartanMatrix.E₆_transpose E6_positive_definite
        E6Base E6Index K 0 5 (by rw [E6_cartan];decide)).eq.symm
  · change canonicalWeyl rawData K 4*(canonicalWeyl rawData K 2*1)=
      canonicalWeyl rawData K 2*(canonicalWeyl rawData K 4*1)
    simpa only [mul_one] using
      (orthogonal_weyls CartanMatrix.E₆ CartanMatrix.E₆_transpose E6_positive_definite
        E6Base E6Index K 2 4 (by rw [E6_cartan];decide)).eq.symm
  · rfl
  · rfl

private theorem raw_word_append (K : Type) [CommRing K] (v w : List (Fin 6)) :
    canonicalWord rawData K (v++w)=canonicalWord rawData K v*canonicalWord rawData K w := by
  induction v with
  | nil=>simp only [List.nil_append,canonicalWord,one_mul]
  | cons i v ih=>rw [List.cons_append,canonicalWord,ih,canonicalWord,mul_assoc]

theorem relative_word_fixed (K : Type) [CommRing K] (sigma : K≃+*K) (r : List (Fin 4)) :
    unitTwist K sigma (canonicalWord rawData K (expandRelative r))=
      canonicalWord rawData K (expandRelative r) := by
  induction r with
  | nil=>simp only [expandRelative,canonicalWord,map_one]
  | cons a r ih=>
    rw [expandRelative,raw_word_append,map_mul,orbit_word_fixed,ih]

theorem matrixWord_fixed (K : Type) [Field K] (sigma : K≃+*K) (r : List (Fin 4)) :
    matrixGroupTwist K sigma (matrixWord K (expandRelative r))=matrixWord K (expandRelative r) := by
  apply Subtype.ext
  change unitTwist K sigma (matrixWord K (expandRelative r)).val=(matrixWord K (expandRelative r)).val
  rw [matrixWord_val,relative_word_fixed]

theorem matrixTransport_fixed (q : CFSG.PrimePower) (sigma : q.Extension 2≃+*q.Extension 2)
    (k : PositiveRoot) :
    matrixGroupTwist (q.Extension 2) sigma (matrixTransport q k)=matrixTransport q k := by
  dsimp only [matrixTransport]
  rw [map_inv,matrixWord_fixed]

end SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckRelativeWordTwist
