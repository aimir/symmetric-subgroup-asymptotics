import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckOrthogonalAdjointTriple
import SymmetricSubgroupAsymptotics.CFSGReeFFourOuterUnipotentGeneration

/-! The literal signed original outer Ree word restricts to the
coefficient-one adjoint triple at E6 node zero. Its other two factors
fix this triple integrally, before any characteristic-two reduction. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix Classical
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourOuterAdjointTriple
open CFSGReeFFourFieldParameters CFSGReeFFourOuterUnipotentGeneration
open CFSGTwistedE6GeckDiagramCovariance CFSGTwistedE6WeylChamber
open CFSGFFourOriginalMiddleWords CFSGFFourE6FixedGeneratedGroup
open CFSGNormTwoGeckOrthogonalAdjointTriple CFSGNormTwoGeckColumns
open CFSGNormTwoRootPairing CFSGIntegerMatrixPairing CFSGSerreQuadraticMatrix
open CFSGExceptionalCartanPositiveDefinite CFSGExceptionalNormTwoBases
local notation "A" => CartanMatrix.E₆
local notation "hs" => CartanMatrix.E₆_transpose
local notation "hp" => E6_positive_definite
local notation "R" => CFSGTwistedE6GeckDiagramCovariance.rawData
local instance : DecidableEq (Roots A) := Classical.decEq _

def tripleCartan (m : ℕ) : GeckIndex→Field m := Pi.single (Sum.inl (E6Index 0)) 1

def triplePositive (m : ℕ) : GeckIndex→Field m := Pi.single (Sum.inr (E6Index 0 : Roots A)) 1

def tripleNegative (m : ℕ) : GeckIndex→Field m :=
  Pi.single (Sum.inr (negativeIndex A hs hp (E6Index 0))) 1

def rawSignedOuter (m : ℕ) (neg : Bool) (a : Field m) : (Matrix GeckIndex GeckIndex (Field m))ˣ :=
  canonicalRoot R (Field m) neg 0 a*canonicalRoot R (Field m) neg 5 a*
    canonicalRoot R (Field m) neg 1 (alpha m a)

theorem rawHom_signedOuterWord (m : ℕ) (neg : Bool) (a : Field m) :
    rawHom (Field m) (signedOuterWord m neg a)=rawSignedOuter m neg a := by
  simp only [signedOuterWord,map_mul,rawHom_root,folded_root_eq_orbitParameter]
  rfl

private theorem pairing_five_zero :
    integerPairing A (E6Index 5 : Roots A).val (E6Index 0 : Roots A).val=0 := by
  change integerPairing A (Pi.single 5 (1:ℤ) : Fin 6→ℤ) (Pi.single 0 (1:ℤ) : Fin 6→ℤ)=0
  decide

private theorem pairing_one_zero :
    integerPairing A (E6Index 1 : Roots A).val (E6Index 0 : Roots A).val=0 := by
  change integerPairing A (Pi.single 1 (1:ℤ) : Fin 6→ℤ) (Pi.single 0 (1:ℤ) : Fin 6→ℤ)=0
  decide

theorem rawSignedOuter_triple_restriction (m : ℕ) (neg : Bool) (a : Field m) :
    ((rawSignedOuter m neg a : Matrix GeckIndex GeckIndex (Field m))*ᵥtripleCartan m=
      (canonicalRoot R (Field m) neg 0 a : Matrix GeckIndex GeckIndex (Field m))*ᵥtripleCartan m) ∧
    ((rawSignedOuter m neg a : Matrix GeckIndex GeckIndex (Field m))*ᵥtriplePositive m=
      (canonicalRoot R (Field m) neg 0 a : Matrix GeckIndex GeckIndex (Field m))*ᵥtriplePositive m) ∧
    ((rawSignedOuter m neg a : Matrix GeckIndex GeckIndex (Field m))*ᵥtripleNegative m=
      (canonicalRoot R (Field m) neg 0 a : Matrix GeckIndex GeckIndex (Field m))*ᵥtripleNegative m) := by
  have h5 := orthogonal_root_fixes_adjoint_triple A hs hp E6Base E6Index
    (Field m) 5 0 pairing_five_zero neg a
  have h1 := orthogonal_root_fixes_adjoint_triple A hs hp E6Base E6Index
    (Field m) 1 0 pairing_one_zero neg (alpha m a)
  change
    ((canonicalRoot R (Field m) neg 5 a : Matrix GeckIndex GeckIndex (Field m))*ᵥtripleCartan m=
      tripleCartan m) ∧
    ((canonicalRoot R (Field m) neg 5 a : Matrix GeckIndex GeckIndex (Field m))*ᵥtriplePositive m=
      triplePositive m) ∧
    ((canonicalRoot R (Field m) neg 5 a : Matrix GeckIndex GeckIndex (Field m))*ᵥtripleNegative m=
      tripleNegative m) at h5
  change
    ((canonicalRoot R (Field m) neg 1 (alpha m a) : Matrix GeckIndex GeckIndex (Field m))*ᵥtripleCartan m=
      tripleCartan m) ∧
    ((canonicalRoot R (Field m) neg 1 (alpha m a) : Matrix GeckIndex GeckIndex (Field m))*ᵥtriplePositive m=
      triplePositive m) ∧
    ((canonicalRoot R (Field m) neg 1 (alpha m a) : Matrix GeckIndex GeckIndex (Field m))*ᵥtripleNegative m=
      tripleNegative m) at h1
  simp only [rawSignedOuter,Units.val_mul,←Matrix.mulVec_mulVec,
    h1.1,h5.1,h1.2.1,h5.2.1,h1.2.2,h5.2.2,and_self]

end SymmetricSubgroupAsymptotics.CFSGReeFFourOuterAdjointTriple
