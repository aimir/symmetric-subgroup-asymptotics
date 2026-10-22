import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckLatticeDegree
import SymmetricSubgroupAsymptotics.CFSGGradedMatrixDiagonalKernel

/-! The actual original Geck lattice grading has singleton nonzero fibres.
Consequently a subgroup preserving each root degree and fixing the original
Cartan columns is abelian, in every characteristic. The hypotheses are
literal column statements; word kernels must establish them separately. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoGeckDiagonalKernel
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing CFSGNormTwoGeckLatticeDegree
open CFSGGradedMatrixSupport
variable {n : Type} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℤ) (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    [Fintype (Roots A)] [DecidableEq (Roots A)]
    (b : (rootPairing A hs hp).Base)

theorem lattice_nonzero_fibres (i j : b.support⊕Roots A)
    (he : latticeWeight A hs hp b i=latticeWeight A hs hp b j)
    (hj : latticeWeight A hs hp b j≠0) : i=j := by
  cases i with
  | inl i=> exact False.elim (hj he.symm)
  | inr i=>
    cases j with
    | inl j=> exact False.elim (hj rfl)
    | inr j=> exact congrArg Sum.inr (Subtype.ext he)

theorem subgroup_soluble_of_root_degrees_of_cartan_fixed (K : Type) [CommRing K]
    (H : Subgroup ((Matrix (b.support⊕Roots A) (b.support⊕Roots A) K)ˣ))
    (hdegree : ∀g∈H,Supported (latticeWeight A hs hp b) id
      (g : Matrix (b.support⊕Roots A) (b.support⊕Roots A) K))
    (hcartan : ∀g∈H,∀j : b.support,
      (g : Matrix (b.support⊕Roots A) (b.support⊕Roots A) K)*ᵥPi.single (.inl j) 1=
        Pi.single (.inl j) 1) : IsSolvable H := by
  apply subgroup_soluble_of_preserves_of_fixes_zero (latticeWeight A hs hp b)
    (lattice_nonzero_fibres A hs hp b) H hdegree
  intro g hg j hj
  cases j with
  | inl j=>exact hcartan g hg j
  | inr j=>
    change j.val=0 at hj
    have hn := j.property
    rw [hj] at hn
    norm_num [integerPairing] at hn

end SymmetricSubgroupAsymptotics.CFSGNormTwoGeckDiagonalKernel
