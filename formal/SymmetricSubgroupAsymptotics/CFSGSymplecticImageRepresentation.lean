import SymmetricSubgroupAsymptotics.CFSGSymplecticRootIntertwining
import SymmetricSubgroupAsymptotics.CFSGSerreImageRepresentation
import SymmetricSubgroupAsymptotics.CFSGSerreRootOperatorInvertible

/-! An actual representation of the pinned type-C root-generated model
on the image of its genuine integral matrix representation. Its original
roots act by literal symplectic transvection conjugation on that image. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGSymplecticSerreMatrices
open CFSG.Models.Chevalley CFSGSerreLocalNilpotence

def symplecticImageRepresentation (K : Type) [Field K] (r : ℕ) :
    Model (CartanMatrix.C r).transpose K →*
      ((symplecticBaseChange K r).range ≃ₗ[K] (symplecticBaseChange K r).range) :=
  CFSGSerreImageRepresentation.imageRepresentation (CartanMatrix.C r).transpose K
    (symplecticBaseChange K r)
    (fun neg i k => CFSGIntegralSquareZeroOperators.operator K (rootMatrix K r neg i) k)
    (symplecticBaseChange_operator K r)

theorem symplecticImageRepresentation_intertwines (K : Type) [Field K] (r : ℕ)
    (g : Model (CartanMatrix.C r).transpose K)
    (x : Space (CartanMatrix.C r).transpose K) :
    (symplecticImageRepresentation K r g ((symplecticBaseChange K r).rangeRestrict x)).val =
      symplecticBaseChange K r (g.val x) :=
  CFSGSerreImageRepresentation.imageRepresentation_intertwines
    (CartanMatrix.C r).transpose K (symplecticBaseChange K r)
    (fun neg i k => CFSGIntegralSquareZeroOperators.operator K (rootMatrix K r neg i) k)
    (symplecticBaseChange_operator K r) g x

theorem symplecticImageRepresentation_root (K : Type) [Field K] (r : ℕ)
    (neg : Bool) (i : Fin r) (t : K) (y : (symplecticBaseChange K r).range) :
    (symplecticImageRepresentation K r
      ⟨rootEquiv (CartanMatrix.C r).transpose K neg i t,
        rootEquiv_mem_model (CartanMatrix.C r).transpose K neg i t⟩ y).val =
      (1 + t • rootMatrix K r neg i) * y.val * (1 - t • rootMatrix K r neg i) := by
  obtain ⟨x, hx⟩ := y.property
  have hy : y = (symplecticBaseChange K r).rangeRestrict x := by
    apply Subtype.ext
    exact hx.symm
  rw [hy, symplecticImageRepresentation_intertwines]
  change symplecticBaseChange K r
    (rootOperator (CartanMatrix.C r).transpose K neg i t x) = _
  exact symplecticBaseChange_rootOperator K r neg i t x

end SymmetricSubgroupAsymptotics.CFSGSymplecticSerreMatrices
