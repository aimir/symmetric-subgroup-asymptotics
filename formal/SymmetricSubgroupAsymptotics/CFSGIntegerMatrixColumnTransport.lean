import SymmetricSubgroupAsymptotics.CFSGIntegerMatrixPairing

/-! Rational column identities for literal integer matrices descend to the
integer columns and then to every coefficient ring. No division is used
after the integer identity has been recovered. -/
set_option autoImplicit false
set_option Elab.async false
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGIntegerMatrixColumnTransport
variable {I : Type*} [Fintype I] [DecidableEq I]

def integerVector (K : Type*) [CommRing K] (v : I→ℤ) : I→K := fun i=>(v i:K)

theorem integerVector_rat_injective : Function.Injective (integerVector (I:=I) ℚ) := by
  intro v w h
  ext i
  apply (Int.cast_injective : Function.Injective (Int.cast : ℤ→ℚ))
  exact congrFun h i

theorem map_mulVec (K : Type*) [CommRing K] (M : Matrix I I ℤ) (v : I→ℤ) :
    (Int.castRingHom K).mapMatrix M*ᵥintegerVector K v=integerVector K (M*ᵥv) := by
  funext i
  exact (RingHom.map_mulVec (Int.castRingHom K) M v i).symm

theorem integral_column_of_rational (M : Matrix I I ℤ) (v w : I→ℤ)
    (h : (Int.castRingHom ℚ).mapMatrix M*ᵥintegerVector ℚ v=integerVector ℚ w) : M*ᵥv=w := by
  apply integerVector_rat_injective
  rw [←map_mulVec ℚ M v]
  exact h

theorem column_of_rational (K : Type*) [CommRing K] (M : Matrix I I ℤ) (v w : I→ℤ)
    (h : (Int.castRingHom ℚ).mapMatrix M*ᵥintegerVector ℚ v=integerVector ℚ w) :
    (Int.castRingHom K).mapMatrix M*ᵥintegerVector K v=integerVector K w := by
  rw [map_mulVec,integral_column_of_rational M v w h]

@[simp] theorem integerVector_single (K : Type*) [CommRing K] (i : I) (z : ℤ) :
    integerVector K (Pi.single i z)=Pi.single i (z:K) := by
  ext j
  simp [integerVector,Pi.single_apply]

@[simp] theorem integerVector_add (K : Type*) [CommRing K] (v w : I→ℤ) :
    integerVector K (v+w)=integerVector K v+integerVector K w := by ext i;simp [integerVector]

@[simp] theorem integerVector_neg (K : Type*) [CommRing K] (v : I→ℤ) :
    integerVector K (-v)= -integerVector K v := by ext i;simp [integerVector]

@[simp] theorem integerVector_zsmul (K : Type*) [CommRing K] (z : ℤ) (v : I→ℤ) :
    integerVector K (z • v)=(z:K) • integerVector K v := by
  ext i
  simp [integerVector,Pi.smul_apply]

end SymmetricSubgroupAsymptotics.CFSGIntegerMatrixColumnTransport
