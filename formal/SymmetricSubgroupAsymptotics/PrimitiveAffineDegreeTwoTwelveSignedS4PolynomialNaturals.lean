import SymmetricSubgroupAsymptotics.LiteralBinaryPolynomialWordCertificate
import SymmetricSubgroupAsymptotics.BinaryBitmaskCoordinates
import SymmetricSubgroupAsymptotics.DerivedGeneratorWords
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelvePairFiniteCatalogueRows51To100
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelvePairFiniteCatalogueRows101To150
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveRow64PolynomialNatural

/-! Literal two-generator polynomial certificates for nine signed-S4 rows.
Each new row uses the same checked algebra-word certificate theorem. The
finite recurrence and inverse tables reconstruct every original coordinate;
no original group closure or invariant-submodule census is assumed. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace SymmetricSubgroupAsymptotics
namespace PrimitiveAffineDegreeTwoTwelveSignedS4PolynomialNaturals
open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
open DegreeTwoTwelvePairFiniteCatalogue

theorem row64Natural : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) row64Interface.top (Fin 12)) 2 :=
  PrimitiveAffineDegreeTwoTwelveRow64PolynomialNatural.row64Natural

namespace Row66

def columns (i : Fin 12) : ℕ := (#[14, 8, 16, 3328, 641, 1024, 512, 2561, 3073, 44, 82, 22] : Array ℕ)[i.val]!
def operator : Module.End (ZMod 2) (Fin 12 → ZMod 2) :=
  (binaryMatrixOfColumnMasks 12 columns).mulVecLin
def vectors (j : Fin 2) (m : Fin 12) : Fin 12 → ZMod 2 :=
  binaryVectorOfMask 12 (((#[#[1, 14, 3352, 964, 1084, 3011, 1084, 3011, 1084, 3011, 1084, 3011], #[32, 1024, 82, 137, 1807, 361, 1807, 361, 1807, 361, 1807, 361]] : Array (Array ℕ))[j.val]!)[m.val]!)
def selected (i : Fin 12) : Fin 2 × Fin 12 :=
  (![0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1] i, ![0, 1, 2, 3, 4, 5, 0, 1, 2, 3, 4, 5] i)
def coefficient (i : Fin 12) : Fin 12 → ZMod 2 :=
  binaryVectorOfMask 12 ((#[1, 1882, 2540, 3764, 1928, 64, 466, 3253, 1831, 932, 128, 3743] : Array ℕ)[i.val]!)
private theorem step_checked : ∀ (j : Fin 2) (m : Fin 11) (x : Fin 12),
    vectors j m.succ x = operator (vectors j m.castSucc) x := by
  decide +kernel
def witness : LiteralPolynomialSpanWitness operator 2 11 where
  vectors := vectors
  step j m := funext (step_checked j m)
  selected := selected
  coefficient := coefficient
  point_eq := by decide +kernel

def words : Fin 3 → row66Interface.top := ![(closureGenerators row66Generators 0) * (closureGenerators row66Generators 3) * (closureGenerators row66Generators 1), (closureGenerators row66Generators 2), (closureGenerators row66Generators 0) * (closureGenerators row66Generators 1) * (closureGenerators row66Generators 0)]
theorem row66Natural : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) row66Interface.top (Fin 12)) 2 := by
  apply LiteralBinaryPolynomialWordCertificate.uniform_of_basis _ words operator witness
  decide +kernel

end Row66

theorem row66Natural : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) row66Interface.top (Fin 12)) 2 :=
  Row66.row66Natural

namespace Row102

def columns (i : Fin 12) : ℕ := (#[16, 32, 64, 128, 256, 512, 1024, 1, 2048, 4, 2, 8] : Array ℕ)[i.val]!
def operator : Module.End (ZMod 2) (Fin 12 → ZMod 2) :=
  (binaryMatrixOfColumnMasks 12 columns).mulVecLin
def vectors (j : Fin 2) (m : Fin 12) : Fin 12 → ZMod 2 :=
  binaryVectorOfMask 12 (((#[#[1, 16, 256, 2048, 8, 128, 1, 16, 256, 2048, 8, 128], #[2, 32, 512, 4, 64, 1024, 2, 32, 512, 4, 64, 1024]] : Array (Array ℕ))[j.val]!)[m.val]!)
def selected (i : Fin 12) : Fin 2 × Fin 12 :=
  (![0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1] i, ![0, 1, 2, 3, 4, 5, 0, 1, 2, 3, 4, 5] i)
def coefficient (i : Fin 12) : Fin 12 → ZMod 2 :=
  binaryVectorOfMask 12 ((#[1, 64, 512, 16, 2, 128, 1024, 32, 4, 256, 2048, 8] : Array ℕ)[i.val]!)
private theorem step_checked : ∀ (j : Fin 2) (m : Fin 11) (x : Fin 12),
    vectors j m.succ x = operator (vectors j m.castSucc) x := by
  decide +kernel
def witness : LiteralPolynomialSpanWitness operator 2 11 where
  vectors := vectors
  step j m := funext (step_checked j m)
  selected := selected
  coefficient := coefficient
  point_eq := by decide +kernel

def words : Fin 1 → row102Interface.top := ![(closureGenerators row102Generators 0) * (closureGenerators row102Generators 1)]
theorem row102Natural : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) row102Interface.top (Fin 12)) 2 := by
  apply LiteralBinaryPolynomialWordCertificate.uniform_of_basis _ words operator witness
  decide +kernel

end Row102

theorem row102Natural : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) row102Interface.top (Fin 12)) 2 :=
  Row102.row102Natural

namespace Row110

def columns (i : Fin 12) : ℕ := (#[2312, 844, 1202, 3218, 781, 1058, 580, 659, 3340, 684, 1362, 145] : Array ℕ)[i.val]!
def operator : Module.End (ZMod 2) (Fin 12 → ZMod 2) :=
  (binaryMatrixOfColumnMasks 12 columns).mulVecLin
def vectors (j : Fin 2) (m : Fin 12) : Fin 12 → ZMod 2 :=
  binaryVectorOfMask 12 (((#[#[2, 844, 1476, 3131, 1082, 3491, 1082, 3491, 1082, 3491, 1082, 3491], #[8, 3218, 1809, 247, 2318, 1777, 2318, 1777, 2318, 1777, 2318, 1777]] : Array (Array ℕ))[j.val]!)[m.val]!)
def selected (i : Fin 12) : Fin 2 × Fin 12 :=
  (![0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1] i, ![0, 1, 2, 3, 4, 5, 0, 1, 2, 3, 4, 5] i)
def coefficient (i : Fin 12) : Fin 12 → ZMod 2 :=
  binaryVectorOfMask 12 ((#[302, 1, 1549, 64, 3928, 3500, 2972, 3146, 890, 3753, 677, 310] : Array ℕ)[i.val]!)
private theorem step_checked : ∀ (j : Fin 2) (m : Fin 11) (x : Fin 12),
    vectors j m.succ x = operator (vectors j m.castSucc) x := by
  decide +kernel
def witness : LiteralPolynomialSpanWitness operator 2 11 where
  vectors := vectors
  step j m := funext (step_checked j m)
  selected := selected
  coefficient := coefficient
  point_eq := by decide +kernel

def words : Fin 9 → row110Interface.top := ![(closureGenerators row110Generators 3), (closureGenerators row110Generators 3) * (closureGenerators row110Generators 0), (closureGenerators row110Generators 1) * (closureGenerators row110Generators 1), (closureGenerators row110Generators 4) * (closureGenerators row110Generators 3), (closureGenerators row110Generators 0) * (closureGenerators row110Generators 1) * (closureGenerators row110Generators 0), (closureGenerators row110Generators 3) * (closureGenerators row110Generators 4), (closureGenerators row110Generators 2) * (closureGenerators row110Generators 1), (closureGenerators row110Generators 4) * (closureGenerators row110Generators 2), (closureGenerators row110Generators 1) * (closureGenerators row110Generators 4)]
theorem row110Natural : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) row110Interface.top (Fin 12)) 2 := by
  apply LiteralBinaryPolynomialWordCertificate.uniform_of_basis _ words operator witness
  decide +kernel

end Row110

theorem row110Natural : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) row110Interface.top (Fin 12)) 2 :=
  Row110.row110Natural

namespace Row111

def columns (i : Fin 12) : ℕ := (#[2136, 12, 18, 1018, 1532, 4032, 1953, 1176, 792, 270, 150, 57] : Array ℕ)[i.val]!
def operator : Module.End (ZMod 2) (Fin 12 → ZMod 2) :=
  (binaryMatrixOfColumnMasks 12 columns).mulVecLin
def vectors (j : Fin 2) (m : Fin 12) : Fin 12 → ZMod 2 :=
  binaryVectorOfMask 12 (((#[#[1, 2136, 414, 408, 390, 1950, 0, 0, 0, 0, 0, 0], #[2, 12, 1000, 3349, 3585, 2553, 390, 1950, 0, 0, 0, 0]] : Array (Array ℕ))[j.val]!)[m.val]!)
def selected (i : Fin 12) : Fin 2 × Fin 12 :=
  (![0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1] i, ![0, 1, 2, 3, 4, 5, 0, 1, 2, 3, 4, 5] i)
def coefficient (i : Fin 12) : Fin 12 → ZMod 2 :=
  binaryVectorOfMask 12 ((#[1, 64, 76, 204, 216, 2079, 1075, 2932, 2920, 3580, 3544, 1061] : Array ℕ)[i.val]!)
private theorem step_checked : ∀ (j : Fin 2) (m : Fin 11) (x : Fin 12),
    vectors j m.succ x = operator (vectors j m.castSucc) x := by
  decide +kernel
def witness : LiteralPolynomialSpanWitness operator 2 11 where
  vectors := vectors
  step j m := funext (step_checked j m)
  selected := selected
  coefficient := coefficient
  point_eq := by decide +kernel

def words : Fin 12 → row111Interface.top := ![(closureGenerators row111Generators 0) * (closureGenerators row111Generators 1), (closureGenerators row111Generators 2) * (closureGenerators row111Generators 3), (closureGenerators row111Generators 2) * (closureGenerators row111Generators 0), (closureGenerators row111Generators 0) * (closureGenerators row111Generators 1) * (closureGenerators row111Generators 3), (closureGenerators row111Generators 4) * (closureGenerators row111Generators 1), (closureGenerators row111Generators 0) * (closureGenerators row111Generators 2), (closureGenerators row111Generators 1) * (closureGenerators row111Generators 1), (closureGenerators row111Generators 4), (closureGenerators row111Generators 4) * (closureGenerators row111Generators 4), (closureGenerators row111Generators 1) * (closureGenerators row111Generators 4), (closureGenerators row111Generators 0) * (closureGenerators row111Generators 0) * (closureGenerators row111Generators 3), (closureGenerators row111Generators 0)]
theorem row111Natural : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) row111Interface.top (Fin 12)) 2 := by
  apply LiteralBinaryPolynomialWordCertificate.uniform_of_basis _ words operator witness
  decide +kernel

end Row111

theorem row111Natural : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) row111Interface.top (Fin 12)) 2 :=
  Row111.row111Natural

namespace Row114

def columns (i : Fin 12) : ℕ := (#[16, 128, 256, 32, 64, 512, 1024, 4, 2, 1, 2048, 8] : Array ℕ)[i.val]!
def operator : Module.End (ZMod 2) (Fin 12 → ZMod 2) :=
  (binaryMatrixOfColumnMasks 12 columns).mulVecLin
def vectors (j : Fin 2) (m : Fin 12) : Fin 12 → ZMod 2 :=
  binaryVectorOfMask 12 (((#[#[1, 16, 64, 1024, 2048, 8, 32, 512, 1, 16, 64, 1024], #[2, 128, 4, 256, 2, 128, 4, 256, 2, 128, 4, 256]] : Array (Array ℕ))[j.val]!)[m.val]!)
def selected (i : Fin 12) : Fin 2 × Fin 12 :=
  (![0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1] i, ![0, 1, 2, 3, 4, 5, 6, 7, 0, 1, 2, 3] i)
def coefficient (i : Fin 12) : Fin 12 → ZMod 2 :=
  binaryVectorOfMask 12 ((#[1, 256, 1024, 32, 2, 64, 4, 512, 2048, 128, 8, 16] : Array ℕ)[i.val]!)
private theorem step_checked : ∀ (j : Fin 2) (m : Fin 11) (x : Fin 12),
    vectors j m.succ x = operator (vectors j m.castSucc) x := by
  decide +kernel
def witness : LiteralPolynomialSpanWitness operator 2 11 where
  vectors := vectors
  step j m := funext (step_checked j m)
  selected := selected
  coefficient := coefficient
  point_eq := by decide +kernel

def words : Fin 1 → row114Interface.top := ![(closureGenerators row114Generators 2) * (closureGenerators row114Generators 4)]
theorem row114Natural : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) row114Interface.top (Fin 12)) 2 := by
  apply LiteralBinaryPolynomialWordCertificate.uniform_of_basis _ words operator witness
  decide +kernel

end Row114

theorem row114Natural : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) row114Interface.top (Fin 12)) 2 :=
  Row114.row114Natural

namespace Row115

def columns (i : Fin 12) : ℕ := (#[17, 80, 40, 258, 132, 544, 1088, 513, 3072, 260, 130, 2056] : Array ℕ)[i.val]!
def operator : Module.End (ZMod 2) (Fin 12 → ZMod 2) :=
  (binaryMatrixOfColumnMasks 12 columns).mulVecLin
def vectors (j : Fin 2) (m : Fin 12) : Fin 12 → ZMod 2 :=
  binaryVectorOfMask 12 (((#[#[1, 17, 149, 700, 139, 834, 2324, 1188, 139, 834, 2324, 1188], #[2, 80, 1220, 1771, 1188, 139, 834, 2324, 1188, 139, 834, 2324]] : Array (Array ℕ))[j.val]!)[m.val]!)
def selected (i : Fin 12) : Fin 2 × Fin 12 :=
  (![0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1] i, ![0, 1, 2, 3, 4, 5, 6, 7, 0, 1, 2, 3] i)
def coefficient (i : Fin 12) : Fin 12 → ZMod 2 :=
  binaryVectorOfMask 12 ((#[1, 256, 3340, 3099, 3, 1667, 515, 3338, 2486, 2709, 1541, 1273] : Array ℕ)[i.val]!)
private theorem step_checked : ∀ (j : Fin 2) (m : Fin 11) (x : Fin 12),
    vectors j m.succ x = operator (vectors j m.castSucc) x := by
  decide +kernel
def witness : LiteralPolynomialSpanWitness operator 2 11 where
  vectors := vectors
  step j m := funext (step_checked j m)
  selected := selected
  coefficient := coefficient
  point_eq := by decide +kernel

def words : Fin 6 → row115Interface.top := ![(closureGenerators row115Generators 1) * (closureGenerators row115Generators 3), (closureGenerators row115Generators 0) * (closureGenerators row115Generators 2), (closureGenerators row115Generators 0) * (closureGenerators row115Generators 3) * (closureGenerators row115Generators 1), (closureGenerators row115Generators 1) * (closureGenerators row115Generators 0) * (closureGenerators row115Generators 1), (closureGenerators row115Generators 0) * (closureGenerators row115Generators 0) * (closureGenerators row115Generators 0), (closureGenerators row115Generators 3) * (closureGenerators row115Generators 1)]
theorem row115Natural : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) row115Interface.top (Fin 12)) 2 := by
  apply LiteralBinaryPolynomialWordCertificate.uniform_of_basis _ words operator witness
  decide +kernel

end Row115

theorem row115Natural : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) row115Interface.top (Fin 12)) 2 :=
  Row115.row115Natural

namespace Row146

def columns (i : Fin 12) : ℕ := (#[16, 64, 32, 128, 256, 512, 1024, 1, 2048, 2, 4, 8] : Array ℕ)[i.val]!
def operator : Module.End (ZMod 2) (Fin 12 → ZMod 2) :=
  (binaryMatrixOfColumnMasks 12 columns).mulVecLin
def vectors (j : Fin 2) (m : Fin 12) : Fin 12 → ZMod 2 :=
  binaryVectorOfMask 12 (((#[#[1, 16, 256, 2048, 8, 128, 1, 16, 256, 2048, 8, 128], #[2, 64, 1024, 4, 32, 512, 2, 64, 1024, 4, 32, 512]] : Array (Array ℕ))[j.val]!)[m.val]!)
def selected (i : Fin 12) : Fin 2 × Fin 12 :=
  (![0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1] i, ![0, 1, 2, 3, 4, 5, 0, 1, 2, 3, 4, 5] i)
def coefficient (i : Fin 12) : Fin 12 → ZMod 2 :=
  binaryVectorOfMask 12 ((#[1, 64, 512, 16, 2, 1024, 128, 32, 4, 2048, 256, 8] : Array ℕ)[i.val]!)
private theorem step_checked : ∀ (j : Fin 2) (m : Fin 11) (x : Fin 12),
    vectors j m.succ x = operator (vectors j m.castSucc) x := by
  decide +kernel
def witness : LiteralPolynomialSpanWitness operator 2 11 where
  vectors := vectors
  step j m := funext (step_checked j m)
  selected := selected
  coefficient := coefficient
  point_eq := by decide +kernel

def words : Fin 1 → row146Interface.top := ![(closureGenerators row146Generators 0) * (closureGenerators row146Generators 3)]
theorem row146Natural : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) row146Interface.top (Fin 12)) 2 := by
  apply LiteralBinaryPolynomialWordCertificate.uniform_of_basis _ words operator witness
  decide +kernel

end Row146

theorem row146Natural : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) row146Interface.top (Fin 12)) 2 :=
  Row146.row146Natural

namespace Row149

def columns (i : Fin 12) : ℕ := (#[16, 64, 32, 128, 256, 512, 1024, 1, 2048, 2, 4, 8] : Array ℕ)[i.val]!
def operator : Module.End (ZMod 2) (Fin 12 → ZMod 2) :=
  (binaryMatrixOfColumnMasks 12 columns).mulVecLin
def vectors (j : Fin 2) (m : Fin 12) : Fin 12 → ZMod 2 :=
  binaryVectorOfMask 12 (((#[#[1, 16, 256, 2048, 8, 128, 1, 16, 256, 2048, 8, 128], #[2, 64, 1024, 4, 32, 512, 2, 64, 1024, 4, 32, 512]] : Array (Array ℕ))[j.val]!)[m.val]!)
def selected (i : Fin 12) : Fin 2 × Fin 12 :=
  (![0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1] i, ![0, 1, 2, 3, 4, 5, 0, 1, 2, 3, 4, 5] i)
def coefficient (i : Fin 12) : Fin 12 → ZMod 2 :=
  binaryVectorOfMask 12 ((#[1, 64, 512, 16, 2, 1024, 128, 32, 4, 2048, 256, 8] : Array ℕ)[i.val]!)
private theorem step_checked : ∀ (j : Fin 2) (m : Fin 11) (x : Fin 12),
    vectors j m.succ x = operator (vectors j m.castSucc) x := by
  decide +kernel
def witness : LiteralPolynomialSpanWitness operator 2 11 where
  vectors := vectors
  step j m := funext (step_checked j m)
  selected := selected
  coefficient := coefficient
  point_eq := by decide +kernel

def words : Fin 1 → row149Interface.top := ![(closureGenerators row149Generators 0) * (closureGenerators row149Generators 2)]
theorem row149Natural : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) row149Interface.top (Fin 12)) 2 := by
  apply LiteralBinaryPolynomialWordCertificate.uniform_of_basis _ words operator witness
  decide +kernel

end Row149

theorem row149Natural : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) row149Interface.top (Fin 12)) 2 :=
  Row149.row149Natural

end PrimitiveAffineDegreeTwoTwelveSignedS4PolynomialNaturals
end SymmetricSubgroupAsymptotics
