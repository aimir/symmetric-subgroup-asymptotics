import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckIntegralRealization
import SymmetricSubgroupAsymptotics.CFSGSerreQuadraticCanonicalRoots

/-! Integral Geck opposition swaps both signs of the actual quadratic
root unit over every coefficient ring, including characteristic two. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoGeckFieldOpposition
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing CFSGGeckIntegralMatrices
open CFSGNormTwoGeckIntegralRealization CFSGNormTwoGeckIntegralQuadratic
open CFSGSerreQuadraticMatrix
variable {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℤ) (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    [Fintype (Roots A)] [DecidableEq (Roots A)] [(rootPairing A hs hp).IsIrreducible]
    (b : (rootPairing A hs hp).Base) {r : ℕ} (s : Fin r≃b.support)

theorem omega_square : Omega b*Omega b=1 := by
  apply CFSGSerreSquareZeroMatrix.integerCast_injective (b.support⊕Roots A)
  change (Int.castRingHom ℚ).mapMatrix (Omega b*Omega b)=(Int.castRingHom ℚ).mapMatrix 1
  rw [map_mul,map_one,map_Omega]
  exact RootPairing.GeckConstruction.ω_mul_ω (b:=b)

theorem omega_E (i : b.support) : Omega b*E b i*Omega b=F b i := by
  apply CFSGSerreSquareZeroMatrix.integerCast_injective (b.support⊕Roots A)
  change (Int.castRingHom ℚ).mapMatrix (Omega b*E b i*Omega b)=(Int.castRingHom ℚ).mapMatrix (F b i)
  rw [map_mul,map_mul,map_Omega,map_E,map_F]
  exact CFSGGeckOppositionAlgEquiv.opposition_E b i

theorem omega_F (i : b.support) : Omega b*F b i*Omega b=E b i := by
  apply CFSGSerreSquareZeroMatrix.integerCast_injective (b.support⊕Roots A)
  change (Int.castRingHom ℚ).mapMatrix (Omega b*F b i*Omega b)=(Int.castRingHom ℚ).mapMatrix (E b i)
  rw [map_mul,map_mul,map_Omega,map_F,map_E]
  exact CFSGGeckOppositionAlgEquiv.opposition_F b i

def fieldOmega (K : Type*) [CommRing K] : Matrix (b.support⊕Roots A) (b.support⊕Roots A) K :=
  (Int.castRingHom K).mapMatrix (Omega b)

theorem fieldOmega_square (K : Type*) [CommRing K] :
    fieldOmega A hs hp b K*fieldOmega A hs hp b K=1 := by
  rw [fieldOmega,←map_mul,omega_square,map_one]

def oppositionUnit (K : Type*) [CommRing K] : (Matrix (b.support⊕Roots A) (b.support⊕Roots A) K)ˣ :=
  ⟨fieldOmega A hs hp b K,fieldOmega A hs hp b K,
    fieldOmega_square A hs hp b K,fieldOmega_square A hs hp b K⟩

theorem fieldRoot_conjugate (K : Type*) [CommRing K] (neg : Bool) (i : Fin r) :
    fieldOmega A hs hp b K*fieldRoot (realizationData A hs hp b s) K neg i*
      fieldOmega A hs hp b K=fieldRoot (realizationData A hs hp b s) K (!neg) i := by
  cases neg
  · change (Int.castRingHom K).mapMatrix (Omega b)*
      (Int.castRingHom K).mapMatrix (E b (s i))*(Int.castRingHom K).mapMatrix (Omega b)=
      (Int.castRingHom K).mapMatrix (F b (s i))
    rw [←map_mul,←map_mul,omega_E]
  · change (Int.castRingHom K).mapMatrix (Omega b)*
      (Int.castRingHom K).mapMatrix (F b (s i))*(Int.castRingHom K).mapMatrix (Omega b)=
      (Int.castRingHom K).mapMatrix (E b (s i))
    rw [←map_mul,←map_mul,omega_F]

theorem fieldSecond_conjugate (K : Type*) [CommRing K] (neg : Bool) (i : Fin r) :
    fieldOmega A hs hp b K*fieldSecond (realizationData A hs hp b s) K neg i*
      fieldOmega A hs hp b K=fieldSecond (realizationData A hs hp b s) K (!neg) i := by
  cases neg
  · change (Int.castRingHom K).mapMatrix (Omega b)*
      (Int.castRingHom K).mapMatrix (positiveSecond A hs hp b (s i))*
        (Int.castRingHom K).mapMatrix (Omega b)=
      (Int.castRingHom K).mapMatrix (negativeSecond A hs hp b (s i))
    rw [←map_mul,←map_mul]
    rfl
  · change (Int.castRingHom K).mapMatrix (Omega b)*
      (Int.castRingHom K).mapMatrix (negativeSecond A hs hp b (s i))*
        (Int.castRingHom K).mapMatrix (Omega b)=
      (Int.castRingHom K).mapMatrix (positiveSecond A hs hp b (s i))
    rw [←map_mul,←map_mul]
    congr 1
    unfold negativeSecond
    simp only [←mul_assoc,omega_square,one_mul]
    rw [mul_assoc,omega_square,mul_one]

theorem canonicalRoot_conjugate (K : Type*) [CommRing K] (neg : Bool) (i : Fin r) (t : K) :
    oppositionUnit A hs hp b K*canonicalRoot (realizationData A hs hp b s) K neg i t*
      (oppositionUnit A hs hp b K)⁻¹=canonicalRoot (realizationData A hs hp b s) K (!neg) i t := by
  apply Units.ext
  change fieldOmega A hs hp b K*(1+t • fieldRoot (realizationData A hs hp b s) K neg i+
    t^2 • fieldSecond (realizationData A hs hp b s) K neg i)*fieldOmega A hs hp b K=
      1+t • fieldRoot (realizationData A hs hp b s) K (!neg) i+
        t^2 • fieldSecond (realizationData A hs hp b s) K (!neg) i
  simp only [mul_add,add_mul,mul_one,smul_mul_assoc,mul_smul_comm,
    fieldOmega_square,fieldRoot_conjugate,fieldSecond_conjugate]

end SymmetricSubgroupAsymptotics.CFSGNormTwoGeckFieldOpposition
