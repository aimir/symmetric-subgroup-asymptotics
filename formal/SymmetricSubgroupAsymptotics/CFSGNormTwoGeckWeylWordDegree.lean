import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckWeylDegreeTransport
import SymmetricSubgroupAsymptotics.CFSGGradedQuadraticUnit

/-! Every actual Weyl-word conjugate of an original positive root unit
has its two homogeneous coefficients in degrees beta and 2 beta, where
beta is the SAME word of original integral root reflections. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoGeckWeylWordDegree
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing
open CFSGNormTwoGeckIntegralRealization CFSGNormTwoGeckLatticeDegree
open CFSGNormTwoGeckWeylDegreeTransport CFSGSerreQuadraticMatrix
open CFSGGradedQuadraticUnit
variable {n : Type} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℤ) (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    [Fintype (Roots A)] [DecidableEq (Roots A)] [(rootPairing A hs hp).IsIrreducible]
    (b : (rootPairing A hs hp).Base) {r : ℕ} (s : Fin r≃b.support)

def wordRoot : List (Fin r)→Roots A→Roots A
  | [],k=>k
  | i::w,k=>(rootPairing A hs hp).reflectionPerm (s i) (wordRoot w k)

def wordUnit (K : Type) [Field K] : List (Fin r)→
    (Matrix (b.support⊕Roots A) (b.support⊕Roots A) K)ˣ
  | []=>1
  | i::w=>canonicalWeyl (realizationData A hs hp b s) K i*wordUnit K w

theorem canonicalRoot_quadraticGrade (K : Type) [Field K] (j : Fin r) (t : K) :
    QuadraticGrade (latticeWeight A hs hp b) (s j:Roots A).val
      (canonicalRoot (realizationData A hs hp b s) K false j t) := by
  refine ⟨t • fieldRoot (realizationData A hs hp b s) K false j,
    t^2 • fieldSecond (realizationData A hs hp b s) K false j,
    canonicalRoot_val _ _ _ _ _,?_,?_⟩
  · exact supported_smul _ _ _ (field_E_lattice_support A hs hp b s K j) t
  · apply supported_smul
    simpa only [two_smul] using field_second_lattice_support A hs hp b s K j

theorem word_conjugate_quadraticGrade (K : Type) [Field K]
    (w : List (Fin r)) (j : Fin r) (t : K) :
    QuadraticGrade (latticeWeight A hs hp b) (wordRoot A hs hp b s w (s j)).val
      (wordUnit A hs hp b s K w*
        canonicalRoot (realizationData A hs hp b s) K false j t*
          (wordUnit A hs hp b s K w)⁻¹) := by
  induction w with
  | nil=>
    simpa only [wordUnit,wordRoot,one_mul,mul_one,inv_one] using
      canonicalRoot_quadraticGrade A hs hp b s K j t
  | cons i w ih=>
    have hh := conjugate (latticeWeight A hs hp b)
      (wordRoot A hs hp b s w (s j)).val (reflectionEquiv A (s i))
      (canonicalWeyl (realizationData A hs hp b s) K i)
      (wordUnit A hs hp b s K w*
        canonicalRoot (realizationData A hs hp b s) K false j t*
          (wordUnit A hs hp b s K w)⁻¹)
      (weyl_lattice_support A hs hp b s K i)
      (weyl_inverse_lattice_support A hs hp b s K i) ih
    have he : wordUnit A hs hp b s K (i::w)*
        canonicalRoot (realizationData A hs hp b s) K false j t*
          (wordUnit A hs hp b s K (i::w))⁻¹=
        canonicalWeyl (realizationData A hs hp b s) K i*
          (wordUnit A hs hp b s K w*
            canonicalRoot (realizationData A hs hp b s) K false j t*
              (wordUnit A hs hp b s K w)⁻¹)*
          (canonicalWeyl (realizationData A hs hp b s) K i)⁻¹ := by
      dsimp only [wordUnit]
      group
    rw [he]
    exact hh

end SymmetricSubgroupAsymptotics.CFSGNormTwoGeckWeylWordDegree
