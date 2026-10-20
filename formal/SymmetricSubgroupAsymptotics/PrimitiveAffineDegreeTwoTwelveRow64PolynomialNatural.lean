import SymmetricSubgroupAsymptotics.LiteralBinaryPolynomialWordCertificate
import SymmetricSubgroupAsymptotics.BinaryBitmaskCoordinates
import SymmetricSubgroupAsymptotics.DerivedGeneratorWords
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelvePairFiniteCatalogueRows51To100
/-! A literal polynomial certificate for the original row64 natural module.
The operator is a sum of eight actual generator words. Two short Krylov
chains and an explicit inverse matrix reconstruct all twelve coordinates,
so the polynomial/PID theorem covers every invariant subrepresentation. -/

set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace SymmetricSubgroupAsymptotics
namespace PrimitiveAffineDegreeTwoTwelveRow64PolynomialNatural
open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
open DegreeTwoTwelvePairFiniteCatalogue

def columns (i : Fin 12) : ℕ := (#[2265, 1358, 694, 2112, 33, 2148, 99, 917, 3466, 39, 2118, 2361] : Array ℕ)[i.val]!
def operator : Module.End (ZMod 2) (Fin 12 → ZMod 2) :=
  (binaryMatrixOfColumnMasks 12 columns).mulVecLin
def vectors (j : Fin 2) (m : Fin 12) : Fin 12 → ZMod 2 :=
  binaryVectorOfMask 12 (((#[#[1, 2265, 2679, 3609, 480, 1560, 0, 0, 0, 0, 0, 0], #[8, 2112, 2394, 2559, 2145, 2535, 0, 0, 0, 0, 0, 0]] : Array (Array ℕ))[j.val]!)[m.val]!)
def selected (i : Fin 12) : Fin 2 × Fin 12 :=
  (![0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1] i, ![0, 1, 2, 3, 4, 5, 0, 1, 2, 3, 4, 5] i)
def coefficient (i : Fin 12) : Fin 12 → ZMod 2 :=
  binaryVectorOfMask 12 ((#[1, 1339, 3331, 64, 2624, 1153, 169, 2691, 3771, 1660, 3164, 41] : Array ℕ)[i.val]!)
private theorem step_checked : ∀ (j : Fin 2) (m : Fin 11) (x : Fin 12),
    vectors j m.succ x = operator (vectors j m.castSucc) x := by
  decide +kernel
def witness : LiteralPolynomialSpanWitness operator 2 11 where
  vectors := vectors
  step j m := funext (step_checked j m)
  selected := selected
  coefficient := coefficient
  point_eq := by decide +kernel

def words : Fin 8 → row64Interface.top := ![(closureGenerators row64Generators 1) * (closureGenerators row64Generators 2) * (closureGenerators row64Generators 0), (closureGenerators row64Generators 2) * (closureGenerators row64Generators 2), (closureGenerators row64Generators 0), (closureGenerators row64Generators 0) * (closureGenerators row64Generators 1), (closureGenerators row64Generators 1) * (closureGenerators row64Generators 1) * (closureGenerators row64Generators 0), 1, (closureGenerators row64Generators 0) * (closureGenerators row64Generators 0), (closureGenerators row64Generators 2) * (closureGenerators row64Generators 1)]
theorem row64Natural : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) row64Interface.top (Fin 12)) 2 := by
  apply LiteralBinaryPolynomialWordCertificate.uniform_of_basis _ words operator witness
  decide +kernel
end PrimitiveAffineDegreeTwoTwelveRow64PolynomialNatural
end SymmetricSubgroupAsymptotics
