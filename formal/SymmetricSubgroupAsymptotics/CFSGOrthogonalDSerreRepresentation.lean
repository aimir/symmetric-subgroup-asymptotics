import SymmetricSubgroupAsymptotics.CFSGOrthogonalDSerreCartanAction
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDSerreEF
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDSerrePowers
import SymmetricSubgroupAsymptotics.CFSGSerreGeneratorRepresentation

/-! A genuine representation of the original rational D Serre quotient
on the literal 2r natural matrices. No faithfulness is presumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDSerreMatrices

theorem HE (R : Type*) [CommRing R] (r : ℕ) (hr : 4≤r) (i j : Fin r) :
    ⁅cartan R r i,positive R r j⁆=CartanMatrix.D r i j • positive R r j := by
  have hh := congrArg (Int.castRingHom R).mapMatrix (HE_integer r hr i j)
  simpa only [Ring.lie_def,map_sub,map_mul,map_zsmul,map_cartan,map_positive] using hh

theorem HF (R : Type*) [CommRing R] (r : ℕ) (hr : 4≤r) (i j : Fin r) :
    ⁅cartan R r i,negative R r j⁆=-(CartanMatrix.D r i j • negative R r j) := by
  have hh := congrArg (Int.castRingHom R).mapMatrix (HF_integer r hr i j)
  simpa only [Ring.lie_def,map_sub,map_mul,map_neg,map_zsmul,map_cartan,map_negative] using hh

def rationalOrthogonalRepresentation (r : ℕ) (hr : 4≤r) :
    CFSG.Models.Chevalley.RationalLie (CartanMatrix.D r)→ₗ⁅ℚ⁆Mat ℚ r :=
  CFSGSerreGeneratorRepresentation.rationalRepresentation
    (cartan ℚ r) (positive ℚ r) (negative ℚ r) (CartanMatrix.D r)
    (cartan_cartan ℚ r hr) (EF ℚ r hr) (HE ℚ r hr) (HF ℚ r hr)
    (positive_serre ℚ r hr) (negative_serre ℚ r hr)

@[simp] theorem rationalOrthogonalRepresentation_H (r : ℕ) (hr : 4≤r) (i : Fin r) :
    rationalOrthogonalRepresentation r hr
      (CFSG.Models.Chevalley.generator (CartanMatrix.D r) (CartanMatrix.Generators.H i))=cartan ℚ r i :=
  CFSGSerreGeneratorRepresentation.rationalRepresentation_generator _ _ _ _ _ _ _ _ _ _ _

@[simp] theorem rationalOrthogonalRepresentation_E (r : ℕ) (hr : 4≤r) (i : Fin r) :
    rationalOrthogonalRepresentation r hr
      (CFSG.Models.Chevalley.generator (CartanMatrix.D r) (CartanMatrix.Generators.E i))=positive ℚ r i :=
  CFSGSerreGeneratorRepresentation.rationalRepresentation_generator _ _ _ _ _ _ _ _ _ _ _

@[simp] theorem rationalOrthogonalRepresentation_F (r : ℕ) (hr : 4≤r) (i : Fin r) :
    rationalOrthogonalRepresentation r hr
      (CFSG.Models.Chevalley.generator (CartanMatrix.D r) (CartanMatrix.Generators.F i))=negative ℚ r i :=
  CFSGSerreGeneratorRepresentation.rationalRepresentation_generator _ _ _ _ _ _ _ _ _ _ _

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDSerreMatrices
