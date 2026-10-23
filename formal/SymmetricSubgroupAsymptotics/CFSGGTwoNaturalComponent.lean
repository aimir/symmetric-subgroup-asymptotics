import SymmetricSubgroupAsymptotics.CFSGGTwoNaturalCommutantClassification
import SymmetricSubgroupAsymptotics.CFSGGTwoD4Inclusion
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexRootComponents
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIsometryIndexCrossingSpaces

/-! The extra matrix in the natural Lie commutant crosses exactly one
hyperbolic pair. The literal D4 elementary component excludes it, also
in characteristic two. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGGTwoNaturalComponent
open CFSGGTwoSerreMatrices CFSGGTwoNaturalCommutantClassification CFSGGTwoD4Inclusion
open CFSGOrthogonalDIndexPositiveSpace CFSGOrthogonalDIndexRootComponents
open CFSGOrthogonalDIsometryIndexCrossingSpaces
variable (K : Type) [Field K]

theorem axisSwap_mulVec (v : Index → K) :
    axisSwap K *ᵥ v = fun i => v (Equiv.swap (pos 3) (neg 3) i) := by
  funext i
  simp [axisSwap, Matrix.mulVec, dotProduct]

theorem natural_ne_neg_axisSwap (g : naturalGroup K) :
    (g.val : Mat K) ≠ -axisSwap K := by
  intro hg
  let L := naturalLinearHom K 4 (naturalIntoD4 K g)
  have hact (v : Index → K) : L v = fun i => -v (Equiv.swap (pos 3) (neg 3) i) := by
    change (g.val : Mat K) *ᵥ v = _
    rw [hg, Matrix.neg_mulVec, axisSwap_mulVec]
    rfl
  have hle : (positiveSpace K 4).map L.toLinearMap ≤ crossingSpace K 4 3 := by
    rintro v ⟨u, hu, rfl⟩
    change ∀ i : Fin 4, u (Sum.inr i) = 0 at hu
    change L u (pos 3) = 0 ∧ ∀ i : Fin 4, i ≠ 3 → L u (neg i) = 0
    rw [hact]
    constructor
    · simpa [Equiv.swap_apply_def, pos, neg] using congrArg Neg.neg (hu 3)
    · intro i hi
      simpa [Equiv.swap_apply_def, pos, neg, hi] using congrArg Neg.neg (hu i)
  have heq : (positiveSpace K 4).map L.toLinearMap = crossingSpace K 4 3 :=
    Submodule.eq_of_le_of_finrank_eq hle
      ((L.finrank_map_eq (positiveSpace K 4)).trans
        ((positiveSpace_finrank K 4).trans (crossingSpace_finrank K 4 3).symm))
  have heven := elementary_even_distance K 0 (naturalIntoD4 K g)
  change Even (CFSGOrthogonalDIndexSingularComponents.distance 4
    (positiveSpace K 4) ((positiveSpace K 4).map L.toLinearMap)) at heven
  rw [heq, crossing_distance_one] at heven
  exact (by decide : ¬Even (1 : ℕ)) heven

end SymmetricSubgroupAsymptotics.CFSGGTwoNaturalComponent
