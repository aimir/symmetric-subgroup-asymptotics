import SymmetricSubgroupAsymptotics.CFSGGTwoSerreCartanRelations
import SymmetricSubgroupAsymptotics.CFSGGTwoSerrePowers

/-! A genuine rational representation of the literal pinned G₂ Serre
quotient. Every defining relator is evaluated in the folded D4 matrices;
no source simplicity or faithfulness is used to construct the map. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGGTwoSerreMatrices

def rationalRepresentation : CFSG.Models.Chevalley.RationalLie CartanMatrix.G₂→ₗ⁅ℚ⁆Mat ℚ :=
  CFSGSerreGeneratorRepresentation.rationalRepresentation
    (cartan ℚ) (positive ℚ) (negative ℚ) CartanMatrix.G₂
    (cartan_cartan ℚ) (EF ℚ) (HE ℚ) (HF ℚ) positive_serre negative_serre

@[simp] theorem rationalRepresentation_H (i : Fin 2) :
    rationalRepresentation
      (CFSG.Models.Chevalley.generator CartanMatrix.G₂ (CartanMatrix.Generators.H i))=cartan ℚ i :=
  CFSGSerreGeneratorRepresentation.rationalRepresentation_generator _ _ _ _ _ _ _ _ _ _ _
@[simp] theorem rationalRepresentation_E (i : Fin 2) :
    rationalRepresentation
      (CFSG.Models.Chevalley.generator CartanMatrix.G₂ (CartanMatrix.Generators.E i))=positive ℚ i :=
  CFSGSerreGeneratorRepresentation.rationalRepresentation_generator _ _ _ _ _ _ _ _ _ _ _
@[simp] theorem rationalRepresentation_F (i : Fin 2) :
    rationalRepresentation
      (CFSG.Models.Chevalley.generator CartanMatrix.G₂ (CartanMatrix.Generators.F i))=negative ℚ i :=
  CFSGSerreGeneratorRepresentation.rationalRepresentation_generator _ _ _ _ _ _ _ _ _ _ _

end SymmetricSubgroupAsymptotics.CFSGGTwoSerreMatrices
