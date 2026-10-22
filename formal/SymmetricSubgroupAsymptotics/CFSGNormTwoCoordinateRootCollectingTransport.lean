import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateRationalRootCollecting
import SymmetricSubgroupAsymptotics.CFSGIntegerMatrixMultivariateTransport

/-! Integral two-parameter transport of actual simple/positive-root
collecting. This is equality of literal unit words over EVERY commutative
coefficient ring; rational string identities are discharged internally. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateRootCollectingTransport
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing CFSGSerreQuadraticMatrix
open CFSGNormTwoGeckIntegralRealization CFSGNormTwoCoordinateSelectedRootElement
variable {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ) (hd : ∀i,A i i=2)
    (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    (ho : ∀i j,i≠j→A i j≤0)
    [Fintype (Roots A)] [DecidableEq (Roots A)]
    [(rootPairing A hs hp).IsReduced] [(rootPairing A hs hp).IsIrreducible]

local notation "b₀" => coordinateBase A hd hs hp ho
local notation "s₀" => coordinateIndexEquiv A hd hs hp ho
local notation "D" => realizationData A hs hp b₀ s₀
private abbrev CoordMat (K : Type) := Matrix ((b₀).support⊕Roots A) ((b₀).support⊕Roots A) K

def positiveRootCommutator (K : Type) [CommRing K] (k : Roots A) (i : Fin r) (t a : K) :
    (CoordMat A hd hs hp ho K)ˣ :=
  canonicalRoot D K false i t*selectedRootElement A hd hs hp ho K k a*
    (canonicalRoot D K false i t)⁻¹*(selectedRootElement A hd hs hp ho K k a)⁻¹

def weylSelectedRootElement (K : Type) [CommRing K] (k : Roots A) (i : Fin r) (a : K) :
    (CoordMat A hd hs hp ho K)ˣ :=
  canonicalWeyl D K i*selectedRootElement A hd hs hp ho K k a*(canonicalWeyl D K i)⁻¹

theorem map_positiveRootCommutator_val {K L : Type} [CommRing K] [CommRing L]
    (f : K→+*L) (k : Roots A) (i : Fin r) (t a : K) :
    f.mapMatrix (positiveRootCommutator A hd hs hp ho K k i t a : CoordMat A hd hs hp ho K)=
      (positiveRootCommutator A hd hs hp ho L k i (f t) (f a) : CoordMat A hd hs hp ho L) := by
  simp only [positiveRootCommutator,Units.val_mul,canonicalRoot_inverse,
    selectedRootElement_inverse,map_mul,map_canonicalRoot_val,map_selectedRootElement_val,map_neg]

theorem map_weylSelectedRootElement_val {K L : Type} [CommRing K] [CommRing L]
    (f : K→+*L) (k : Roots A) (i : Fin r) (a : K) :
    f.mapMatrix (weylSelectedRootElement A hd hs hp ho K k i a : CoordMat A hd hs hp ho K)=
      (weylSelectedRootElement A hd hs hp ho L k i (f a) : CoordMat A hd hs hp ho L) := by
  simp only [weylSelectedRootElement,canonicalWeyl,mul_inv_rev,Units.val_mul,
    canonicalRoot_inverse,map_mul,map_canonicalRoot_val,map_selectedRootElement_val,map_one,map_neg]

theorem simple_positive_collecting (K : Type) [CommRing K] (k : Roots A)
    (hk : ∀t,0≤k.val t) (i : Fin r)
    (hpair : integerPairing A k.val (s₀ i:Roots A).val= -1) (t a : K) :
    positiveRootCommutator A hd hs hp ho K k i t a=
      weylSelectedRootElement A hd hs hp ho K k i (a*t) := by
  let M : CoordMat A hd hs hp ho (MvPolynomial (Fin 2) ℤ) :=
    positiveRootCommutator A hd hs hp ho (MvPolynomial (Fin 2) ℤ) k i
      (MvPolynomial.X 0) (MvPolynomial.X 1)
  let N : CoordMat A hd hs hp ho (MvPolynomial (Fin 2) ℤ) :=
    weylSelectedRootElement A hd hs hp ho (MvPolynomial (Fin 2) ℤ) k i
      (MvPolynomial.X 1*MvPolynomial.X 0)
  have hrat : ∀b : Fin 2→ℚ,(MvPolynomial.eval₂Hom (Int.castRingHom ℚ) b).mapMatrix M=
      (MvPolynomial.eval₂Hom (Int.castRingHom ℚ) b).mapMatrix N := by
    intro b
    dsimp only [M,N]
    simpa only [map_positiveRootCommutator_val,map_weylSelectedRootElement_val,map_mul,
      MvPolynomial.eval₂Hom_X'] using
      congrArg (fun u : (CoordMat A hd hs hp ho ℚ)ˣ=>(u : CoordMat A hd hs hp ho ℚ))
        (CFSGNormTwoCoordinateRationalRootCollecting.simple_positive_collecting
          A hd hs hp ho k hk i hpair (b 0) (b 1))
  have hfield := CFSGIntegerMatrixMultivariateTransport.evaluations_eq_of_rational_evaluations
    K M N hrat ![t,a]
  apply Units.ext
  dsimp only [M,N] at hfield
  simpa only [map_positiveRootCommutator_val,map_weylSelectedRootElement_val,map_mul,
    MvPolynomial.eval₂Hom_X',Matrix.cons_val_zero,Matrix.cons_val_one] using hfield

end SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateRootCollectingTransport
