import SymmetricSubgroupAsymptotics.LiteralPolynomialSpanWitness
import SymmetricSubgroupAsymptotics.BinaryBitmaskCoordinates
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoZeroSixteenInterfaces

/-!
# The first zero-core sixteen-point natural module

The literal top is retained. For c = generator 0, a = generator 1 and
b = c*a*c⁻¹, use the group-algebra operator c + 1 + a + b + a*b.
Four initial vectors and their displayed recurrences contain a basis.
The sixteen inverse-matrix rows reconstruct the coordinate vectors.
Every finite obligation below concerns these small displayed arrays.
No invariant-subspace catalogue or rank oracle is a premise.

Literal generator source: PrimitiveAffineSixteenFrameRow1TopCertificate.
Source SHA-256: 5bf601ab955805b0a33767ddbea9f6c8c9fe33fe60d0302164f21d6ed15b3173.
-/

set_option autoImplicit false
noncomputable section
open scoped MonoidAlgebra BigOperators

namespace SymmetricSubgroupAsymptotics
namespace PrimitiveAffineDegreeTwoZeroSixteenRow1AlgebraPolynomial

abbrev Top :=
  Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeTwoZeroSixteenInterfaces.row1.top

def c : Top :=
  ⟨PrimitiveAffineSixteenFrameRow1TopCertificate.generators 0,
    Subgroup.subset_closure ⟨0, rfl⟩⟩

def a : Top :=
  ⟨PrimitiveAffineSixteenFrameRow1TopCertificate.generators 1,
    Subgroup.subset_closure ⟨1, rfl⟩⟩

def b : Top := c * a * c⁻¹

def representation := permutationFunctionRepresentation (ZMod 2) Top (Fin 16)

def operator : Module.End (ZMod 2) (Fin 16 → ZMod 2) :=
  representation c + 1 + representation a + representation b + representation (a * b)

def algebraElement : (ZMod 2)[Top] :=
  MonoidAlgebra.single c 1 + 1 + MonoidAlgebra.single a 1 +
    MonoidAlgebra.single b 1 + MonoidAlgebra.single (a * b) 1

theorem operator_eq : operator = representation.asAlgebraHom algebraElement := by
  simp only [operator, algebraElement, map_add, map_one,
    Representation.asAlgebraHom_single, one_smul]

def vectorMask (j : Fin 4) (m : Fin 6) : ℕ :=
  (#[1057, 32, 8225, 8192, 9217, 1024,
      2, 16714, 4, 4630, 8, 34956,
      16, 4884, 32768, 34968, 256, 49474,
      64, 18754, 4096, 4692, 2048, 39048] : Array ℕ)[6 * j.val + m.val]!

def vectors (j : Fin 4) (m : Fin 6) : Fin 16 → ZMod 2 :=
  binaryVectorOfMask 16 (vectorMask j m)

def selectedSeed : Fin 16 → Fin 4 :=
  ![0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 2, 2, 2, 3, 3, 3]

def selectedPower : Fin 16 → Fin 6 :=
  ![0, 1, 2, 3, 0, 1, 2, 3, 4, 5, 0, 1, 2, 0, 1, 2]

def coefficientMask (i : Fin 16) : ℕ :=
  (#[14, 16, 64, 256, 1024, 2, 8192, 21088,
      2192, 34000, 13, 16672, 32768, 8, 10656, 4096] : Array ℕ)[i.val]!

def coefficient (i : Fin 16) : Fin 16 → ZMod 2 :=
  binaryVectorOfMask 16 (coefficientMask i)

private theorem step_checked : ∀ (j : Fin 4) (m : Fin 5) (x : Fin 16),
    vectors j m.succ x = operator (vectors j m.castSucc) x := by
  decide +kernel

private theorem point_checked : ∀ i x : Fin 16,
    (∑ j, coefficient i j * vectors (selectedSeed j) (selectedPower j) x) =
      (Pi.single i 1 : Fin 16 → ZMod 2) x := by
  decide +kernel

def polynomialWitness : LiteralPolynomialSpanWitness operator 4 5 where
  vectors := vectors
  step j m := by
    funext x
    exact step_checked j m x
  selected j := (selectedSeed j, selectedPower j)
  coefficient := coefficient
  point_eq := point_checked

/-- Every invariant subspace of the actual first zero-core top's natural
binary permutation module has at most four module generators. -/
theorem natural : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) Top (Fin 16)) 4 :=
  polynomialWitness.uniform representation algebraElement operator_eq

end PrimitiveAffineDegreeTwoZeroSixteenRow1AlgebraPolynomial
end SymmetricSubgroupAsymptotics

end
