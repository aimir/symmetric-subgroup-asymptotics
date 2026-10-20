import SymmetricSubgroupAsymptotics.BinaryPlaneWreathNormalGenerators

/-! The literal two-dimensional binary module has no fixed vector under
any nonidentity cubic local matrix. Only the three-point permutation
calculation is finite; arbitrary linear maps are not enumerated. -/
set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.BinaryPlaneNontrivialCubicFixedFree
open BinaryPlanePermutationAffineEquiv BinaryPlaneWreathNormalGenerators

private theorem permutation_fixedFree :
    ∀ (g : Equiv.Perm (Fin 3)) (i : Fin 3),
      g^3=1 → g≠1 → g i≠i := by decide +kernel

theorem fixedFree (L : Linear) (hcubic : L^3=1) (hne : L≠1)
    (v : Plane) (hv : L v=v) : v=0 := by
  by_contra hvne
  have hthree : toThree L ^ 3=1 := by rw [← map_pow,hcubic,map_one]
  have hthree_ne : toThree L≠1 := by
    intro h
    apply hne
    apply toThree_injective
    simpa only [map_one] using h
  have hpoint : nonzeroAction L (⟨v,hvne⟩ : Nonzero) = ⟨v,hvne⟩ :=
    Subtype.ext hv
  apply permutation_fixedFree (toThree L) (nonzeroChart.symm ⟨v,hvne⟩)
    hthree hthree_ne
  change nonzeroChart.symm
    (nonzeroAction L (nonzeroChart (nonzeroChart.symm ⟨v,hvne⟩))) = _
  rw [Equiv.apply_symm_apply,hpoint]

end SymmetricSubgroupAsymptotics.BinaryPlaneNontrivialCubicFixedFree
