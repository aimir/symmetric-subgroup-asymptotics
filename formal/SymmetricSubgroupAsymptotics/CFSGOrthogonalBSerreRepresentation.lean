import SymmetricSubgroupAsymptotics.CFSGOrthogonalBSerreCartanAction
import SymmetricSubgroupAsymptotics.CFSGOrthogonalBSerrePowers
import SymmetricSubgroupAsymptotics.CFSGOrthogonalBMatrixMaps
import SymmetricSubgroupAsymptotics.CFSGSerreGeneratorRepresentation

/-! Genuine rational representation of the original B-transpose Serre
quotient. All six relator families are evaluated in actual matrices. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalBSerreMatrices

theorem HE (R : Type*) [CommRing R] (r : ℕ) (i j : Fin r) :
    ⁅cartan R r i,positive R r j⁆=(CartanMatrix.B r).transpose i j • positive R r j := by
  rw [typeB_transpose]
  have hh := congrArg (Int.castRingHom R).mapMatrix (HE_integer r i j)
  simpa only [Ring.lie_def,map_sub,map_mul,map_zsmul,map_cartan,map_positive] using hh

theorem HF (R : Type*) [CommRing R] (r : ℕ) (i j : Fin r) :
    ⁅cartan R r i,negative R r j⁆= -((CartanMatrix.B r).transpose i j • negative R r j) := by
  rw [typeB_transpose]
  have hh := congrArg (Int.castRingHom R).mapMatrix (HF_integer r i j)
  simpa only [Ring.lie_def,map_sub,map_mul,map_neg,map_zsmul,map_cartan,map_negative] using hh

def rationalOrthogonalRepresentation (r : ℕ) :
    CFSG.Models.Chevalley.RationalLie (CartanMatrix.B r).transpose→ₗ⁅ℚ⁆Mat ℚ r :=
  CFSGSerreGeneratorRepresentation.rationalRepresentation
    (cartan ℚ r) (positive ℚ r) (negative ℚ r) (CartanMatrix.B r).transpose
    (cartan_cartan ℚ r) (EF ℚ r) (HE ℚ r) (HF ℚ r)
    (by rw [typeB_transpose];exact positive_serre ℚ r)
    (by rw [typeB_transpose];exact negative_serre ℚ r)

@[simp] theorem rationalOrthogonalRepresentation_H (r : ℕ) (i : Fin r) :
    rationalOrthogonalRepresentation r
      (CFSG.Models.Chevalley.generator (CartanMatrix.B r).transpose (CartanMatrix.Generators.H i))=cartan ℚ r i :=
  CFSGSerreGeneratorRepresentation.rationalRepresentation_generator _ _ _ _ _ _ _ _ _ _ _
@[simp] theorem rationalOrthogonalRepresentation_E (r : ℕ) (i : Fin r) :
    rationalOrthogonalRepresentation r
      (CFSG.Models.Chevalley.generator (CartanMatrix.B r).transpose (CartanMatrix.Generators.E i))=positive ℚ r i :=
  CFSGSerreGeneratorRepresentation.rationalRepresentation_generator _ _ _ _ _ _ _ _ _ _ _
@[simp] theorem rationalOrthogonalRepresentation_F (r : ℕ) (i : Fin r) :
    rationalOrthogonalRepresentation r
      (CFSG.Models.Chevalley.generator (CartanMatrix.B r).transpose (CartanMatrix.Generators.F i))=negative ℚ r i :=
  CFSGSerreGeneratorRepresentation.rationalRepresentation_generator _ _ _ _ _ _ _ _ _ _ _

end SymmetricSubgroupAsymptotics.CFSGOrthogonalBSerreMatrices
