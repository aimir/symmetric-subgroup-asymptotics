import SymmetricSubgroupAsymptotics.ScalarFourCentralNormalActiveImage
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-! The actual normal active image is killed in the existing scalar space.
Its quotient admits at most d scalar coordinates, with its exact kernel. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.ScalarFourCentralTopCoordinates
open BinaryQuadraticField
variable {Q T : Type} [Group Q] [Group T] {c d : ℕ}

abbrev activeQuotientRank (_D : ScalarFourCentralTopCoordinates Q T c d)
    (S : Submodule Scalar (Fin d → Scalar)) : ℕ :=
  Module.finrank Scalar ((Fin d → Scalar) ⧸ S)

variable (D : ScalarFourCentralTopCoordinates Q T c d)
  (S : Submodule Scalar (Fin d → Scalar))

theorem activeQuotientRank_le : D.activeQuotientRank S≤d := by
  simpa only [Module.finrank_pi,Fintype.card_fin] using S.finrank_quotient_le

def activeQuotientBasis : ((Fin d → Scalar) ⧸ S) ≃ₗ[Scalar]
    (Fin (D.activeQuotientRank S) → Scalar) :=
  (Module.finBasis Scalar ((Fin d → Scalar) ⧸ S)).equivFun

def quotientActive : D.top.ker →* (Fin (D.activeQuotientRank S) → ScalarFour) :=
  (ScalarFourQuadraticField.tupleEquivalence (D.activeQuotientRank S)).symm.toMonoidHom.comp
    ((D.activeQuotientBasis S).toAddEquiv.toMultiplicative.toMonoidHom.comp
      (S.mkQ.toAddMonoidHom.toMultiplicative.comp D.fieldActive))

theorem quotientActive_eq_one_iff (k : D.top.ker) :
    D.quotientActive S k=1 ↔ (D.fieldActive k).toAdd∈S := by
  change (ScalarFourQuadraticField.tupleEquivalence (D.activeQuotientRank S)).symm
    ((D.activeQuotientBasis S).toAddEquiv.toMultiplicative
      (Multiplicative.ofAdd (S.mkQ (D.fieldActive k).toAdd)))=1 ↔ _
  rw [MulEquiv.map_eq_one_iff,MulEquiv.map_eq_one_iff]
  change S.mkQ (D.fieldActive k).toAdd=0 ↔ _
  exact Submodule.Quotient.mk_eq_zero S

end SymmetricSubgroupAsymptotics.ScalarFourCentralTopCoordinates
