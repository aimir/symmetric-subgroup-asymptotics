import SymmetricSubgroupAsymptotics.CFSGFFourSerrePowers
import SymmetricSubgroupAsymptotics.CFSGSerreGeneratorRepresentation

/-! A genuine rational representation of the ORIGINAL pinned F4 Serre
quotient in the actual folded E6 matrices, evaluating all six relators. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGFFourSerreMatrices
local instance fFourRepresentationDecEq : DecidableEq
    (CFSGNormTwoRootPairing.Roots CartanMatrix.E₆) := Classical.decEq _

def rationalRepresentation : CFSG.Models.Chevalley.RationalLie CartanMatrix.F₄→ₗ⁅ℚ⁆Mat :=
  CFSGSerreGeneratorRepresentation.rationalRepresentation
    cartan positive negative CartanMatrix.F₄ HH EF HE HF positive_serre negative_serre

@[simp] theorem rationalRepresentation_H (i : Fin 4) :
    rationalRepresentation (CFSG.Models.Chevalley.generator CartanMatrix.F₄
      (CartanMatrix.Generators.H i))=cartan i :=
  CFSGSerreGeneratorRepresentation.rationalRepresentation_generator _ _ _ _ _ _ _ _ _ _ _
@[simp] theorem rationalRepresentation_E (i : Fin 4) :
    rationalRepresentation (CFSG.Models.Chevalley.generator CartanMatrix.F₄
      (CartanMatrix.Generators.E i))=positive i :=
  CFSGSerreGeneratorRepresentation.rationalRepresentation_generator _ _ _ _ _ _ _ _ _ _ _
@[simp] theorem rationalRepresentation_F (i : Fin 4) :
    rationalRepresentation (CFSG.Models.Chevalley.generator CartanMatrix.F₄
      (CartanMatrix.Generators.F i))=negative i :=
  CFSGSerreGeneratorRepresentation.rationalRepresentation_generator _ _ _ _ _ _ _ _ _ _ _

end SymmetricSubgroupAsymptotics.CFSGFFourSerreMatrices
