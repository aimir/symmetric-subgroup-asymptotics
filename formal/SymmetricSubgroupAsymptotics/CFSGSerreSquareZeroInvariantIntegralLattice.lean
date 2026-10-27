import SymmetricSubgroupAsymptotics.CFSGSerreSquareZeroMatrixOperators

/-! A genuine square-zero Serre realization lands in any actual integral
target lattice containing its generator images and stable under the
literal target divided-power operators. The target need not be a subring.
This is the codomain installer for intrinsic D Cartan lattices.
B uses quadratic-root Data and needs its separately typed analogue. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGSerreSquareZeroInvariantIntegralLattice
open CFSG.Models.Chevalley CFSGSerreSquareZeroMatrix
variable {n : ℕ} {A : Matrix (Fin n) (Fin n) ℤ}
  {I : Type*} [Fintype I] [DecidableEq I] (D : Data A I)
  (N : Submodule ℤ (IntMat I))

theorem rational_lattice_image_mem
    (hgen : ∀ g,D.integerGenerator g∈N)
    (hop : ∀ neg i k X,X∈N→
      CFSGIntegralSquareZeroOperators.operator ℤ (integerRoot D neg i) k X∈N)
    (x : RationalLie A) (hx : x∈integralLattice A) :
    D.rational x∈N.map (integerCast I) := by
  let S : Submodule ℤ (RationalLie A):=
    (N.map (integerCast I)).comap (D.rational.toLinearMap.restrictScalars ℤ)
  have hle : integralLattice A≤S := by
    apply CFSGSerreDiagram.integralLattice_le_of_stable A S
    · intro g
      exact ⟨D.integerGenerator g,hgen g,D.generator_cast g⟩
    · intro neg i k y hy
      change D.rational y∈N.map (integerCast I) at hy
      obtain ⟨X,hX,hcast⟩:=hy
      refine ⟨CFSGIntegralSquareZeroOperators.operator ℤ (integerRoot D neg i) k X,
        hop neg i k X hX,?_⟩
      change (Int.castRingHom ℚ).mapMatrix
        (CFSGIntegralSquareZeroOperators.operator ℤ (integerRoot D neg i) k X)=
          D.rational (dividedPower A neg i k y)
      rw [CFSGIntegralSquareZeroOperators.map_operator,
        CFSGIntegralSquareZeroOperators.operator_changeScalars ℤ ℚ]
      rw [CFSGSerreIntegralRepresentation.dividedPower_intertwines,rational_rootVector,
        CFSGIntegralSquareZeroOperators.rational_operator _ _ (fieldRoot_sq_zero D ℚ neg i)]
      rw [←hcast]
      rfl
  exact hle hx

theorem integral_image_mem
    (hgen : ∀ g,D.integerGenerator g∈N)
    (hop : ∀ neg i k X,X∈N→
      CFSGIntegralSquareZeroOperators.operator ℤ (integerRoot D neg i) k X∈N)
    (x : integralLattice A) : integralRepresentation D x∈N := by
  obtain ⟨Y,hY,hYeq⟩:=rational_lattice_image_mem D N hgen hop x.val x.property
  have he : Y=integralRepresentation D x :=
    integerCast_injective I (hYeq.trans (integralRepresentation_cast D x).symm)
  exact he ▸ hY

end SymmetricSubgroupAsymptotics.CFSGSerreSquareZeroInvariantIntegralLattice
