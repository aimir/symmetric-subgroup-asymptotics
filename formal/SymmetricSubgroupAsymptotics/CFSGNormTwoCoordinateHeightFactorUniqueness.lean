import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateHeightLeadingKernel
import Mathlib.SetTheory.Cardinal.Finite

/-! UNIQUE one-height collection in the actual Geck matrix U. Two
height-h words followed by higher remainders have the same parameters
only when every parameter agrees. The proof uses primitive coefficients
in distinct INTEGER lattice degrees, uniformly in coefficient characteristic. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateHeightFactorUniqueness
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing
open CFSGNormTwoCoordinateRootHeightQuotient CFSGNormTwoCoordinateExactHeightLayer
open CFSGNormTwoCoordinateHeightLayerFactorization CFSGNormTwoCoordinateHeightLeadingKernel
open CFSGNormTwoCoordinateRootHeightLeading CFSGNormTwoCoordinateRootCoefficientCoordinates
variable {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ) (hd : ∀i,A i i=2)
    (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    (ho : ∀i j,i≠j→A i j≤0)
    [Fintype (Roots A)] [DecidableEq (Roots A)]
    [(rootPairing A hs hp).IsReduced] [(rootPairing A hs hp).IsIrreducible]
local notation "b₀" => coordinateBase A hd hs hp ho
private abbrev CoordMat (K : Type) := Matrix ((b₀).support⊕Roots A) ((b₀).support⊕Roots A) K

theorem height_factor_parameters_unique (K : Type) [Field K] (h : ℤ) (hh : 0<h)
    (c d : ExactHeightRoot A h→K) (y z : PositiveGroup A hd hs hp ho K)
    (hy : y∈heightTailInPositive A hd hs hp ho K (h+1))
    (hz : z∈heightTailInPositive A hd hs hp ho K (h+1))
    (he : exactHeightWord A hd hs hp ho K h c*y=exactHeightWord A hd hs hp ho K h d*z) : c=d := by
  classical
  have hlead := congrArg (fun x : PositiveGroup A hd hs hp ho K=>
    CFSGGradedMatrixSingleDegreeSpan.degreePart (heightWeight A hd hs hp ho) h
      ((x.val : CoordMat A hd hs hp ho K)-1)) he
  dsimp only at hlead
  rw [factored_height_leading A hd hs hp ho K h hh c y hy,
    factored_height_leading A hd hs hp ho K h hh d z hz] at hlead
  exact root_family_coefficients_unique A hd hs hp ho K
    (fun k : ExactHeightRoot A h=>k.val.val)
    (fun _ _ hk=>Subtype.ext (Subtype.ext hk)) c d hlead

theorem height_factor_injective (K : Type) [Field K] (h : ℤ) (hh : 0<h) :
    Function.Injective (fun p : (ExactHeightRoot A h→K) × heightTailInPositive A hd hs hp ho K (h+1)=>
      exactHeightWord A hd hs hp ho K h p.1*(p.2 : PositiveGroup A hd hs hp ho K)) := by
  rintro ⟨c,y⟩ ⟨d,z⟩ he
  have hc := height_factor_parameters_unique A hd hs hp ho K h hh c d y.val z.val
    y.property z.property he
  apply Prod.ext hc
  apply Subtype.ext
  exact mul_left_cancel (hc ▸ he)

end SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateHeightFactorUniqueness
