import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateSelectedRootElement
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateNonrootDegreeZero
import SymmetricSubgroupAsymptotics.CFSGIntegerMatrixMultivariateTransport

/-! Positive root elements of pairing zero or one commute in EVERY
characteristic. Their genuine generated-Lie bracket degree has norm four
or six, so its vanishing is proved rather than assumed. Equality of the
two actual integer polynomial words then transports to every ring. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinatePositivePairCommute
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing CFSGSerreQuadraticMatrix
open CFSGNormTwoGeckIntegralRealization CFSGNormTwoGeckLatticeDegree
open CFSGNormTwoCoordinateRootWordString CFSGNormTwoCoordinateSelectedRootElement
open CFSGGradedMatrixSupport CFSGGradedMatrixLieDegree
variable {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ) (hd : ∀i,A i i=2)
    (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    (ho : ∀i j,i≠j→A i j≤0)
    [Fintype (Roots A)] [DecidableEq (Roots A)]
    [(rootPairing A hs hp).IsReduced] [(rootPairing A hs hp).IsIrreducible]

local notation "b₀" => coordinateBase A hd hs hp ho
private abbrev CoordMat (K : Type) := Matrix ((b₀).support⊕Roots A) ((b₀).support⊕Roots A) K

theorem positive_pair_lie_zero (k l : Roots A) (hk : ∀t,0≤k.val t) (hl : ∀t,0≤l.val t)
    (hpair : integerPairing A k.val l.val=0 ∨ integerPairing A k.val l.val=1) :
    ⁅selectedCoefficient A hd hs hp ho k,selectedCoefficient A hd hs hp ho l⁆=0 := by
  apply CFSGNormTwoCoordinateNonrootDegreeZero.nonnegative_norm_four_or_six_degree_zero
    A hd hs hp ho _ (k.val+l.val)
    ((RootPairing.GeckConstruction.lieAlgebra b₀).lie_mem
      (selectedCoefficient_mem A hd hs hp ho k) (selectedCoefficient_mem A hd hs hp ho l))
    (supported_lie (latticeWeight A hs hp b₀) k.val l.val _ _
      (selectedCoefficient_degree A hd hs hp ho k) (selectedCoefficient_degree A hd hs hp ho l))
  · exact fun t=>add_nonneg (hk t) (hl t)
  · simp only [CFSGNormTwoPairingBounds.norm_add A hs,k.property,l.property]
    rcases hpair with h|h <;> simp only [h] <;> norm_num

theorem rational_positive_pair_commute (k l : Roots A) (hk : ∀t,0≤k.val t) (hl : ∀t,0≤l.val t)
    (hpair : integerPairing A k.val l.val=0 ∨ integerPairing A k.val l.val=1) (a b : ℚ) :
    Commute (selectedRootElement A hd hs hp ho ℚ k a) (selectedRootElement A hd hs hp ho ℚ l b) := by
  let X := selectedCoefficient A hd hs hp ho k
  let Y := selectedCoefficient A hd hs hp ho l
  have hc : Commute X Y := sub_eq_zero.mp (positive_pair_lie_zero A hd hs hp ho k l hk hl hpair)
  have hXY : Commute X (1+b • Y+(b^2/2) • Y^2) :=
    ((Commute.one_right X).add_right (hc.smul_right b)).add_right ((hc.pow_right 2).smul_right (b^2/2))
  have hpolynomial : Commute (1+a • X+(a^2/2) • X^2) (1+b • Y+(b^2/2) • Y^2) :=
    ((Commute.one_left _).add_left (hXY.smul_left a)).add_left ((hXY.pow_left 2).smul_left (a^2/2))
  apply Units.ext
  simp only [Units.val_mul,selectedRootElement_val_rational]
  exact hpolynomial.eq

theorem positive_pair_commute (K : Type) [CommRing K] (k l : Roots A)
    (hk : ∀t,0≤k.val t) (hl : ∀t,0≤l.val t)
    (hpair : integerPairing A k.val l.val=0 ∨ integerPairing A k.val l.val=1) (a b : K) :
    Commute (selectedRootElement A hd hs hp ho K k a) (selectedRootElement A hd hs hp ho K l b) := by
  let M : CoordMat A hd hs hp ho (MvPolynomial (Fin 2) ℤ) :=
    (selectedRootElement A hd hs hp ho (MvPolynomial (Fin 2) ℤ) k (MvPolynomial.X 0)*
      selectedRootElement A hd hs hp ho (MvPolynomial (Fin 2) ℤ) l (MvPolynomial.X 1) :
      (CoordMat A hd hs hp ho (MvPolynomial (Fin 2) ℤ))ˣ)
  let N : CoordMat A hd hs hp ho (MvPolynomial (Fin 2) ℤ) :=
    (selectedRootElement A hd hs hp ho (MvPolynomial (Fin 2) ℤ) l (MvPolynomial.X 1)*
      selectedRootElement A hd hs hp ho (MvPolynomial (Fin 2) ℤ) k (MvPolynomial.X 0) :
      (CoordMat A hd hs hp ho (MvPolynomial (Fin 2) ℤ))ˣ)
  have hrat : ∀c : Fin 2→ℚ,(MvPolynomial.eval₂Hom (Int.castRingHom ℚ) c).mapMatrix M=
      (MvPolynomial.eval₂Hom (Int.castRingHom ℚ) c).mapMatrix N := by
    intro c
    dsimp only [M,N]
    simpa only [Units.val_mul,map_mul,map_selectedRootElement_val,MvPolynomial.eval₂Hom_X'] using
      congrArg (fun u : (CoordMat A hd hs hp ho ℚ)ˣ=>(u : CoordMat A hd hs hp ho ℚ))
        (rational_positive_pair_commute A hd hs hp ho k l hk hl hpair (c 0) (c 1)).eq
  have hfield := CFSGIntegerMatrixMultivariateTransport.evaluations_eq_of_rational_evaluations
    K M N hrat ![a,b]
  apply Units.ext
  dsimp only [M,N] at hfield
  simpa only [Units.val_mul,map_mul,map_selectedRootElement_val,MvPolynomial.eval₂Hom_X',
    Matrix.cons_val_zero,Matrix.cons_val_one] using hfield

end SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinatePositivePairCommute
