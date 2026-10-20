import SymmetricSubgroupAsymptotics.ProductBlockFrameGenerators
import SymmetricSubgroupAsymptotics.BinaryPlanePermutationAffineEquiv
import SymmetricSubgroupAsymptotics.AlternatingFourBinaryActualPolynomialUniform

/-! An actual odd subgroup whose quartet image contains the physical
three-cycle has at most eight original point orbits. Local twists may be
arbitrary; all four fibre points are retained over each coarse orbit seed. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.ProductBlockFrame
open BinaryPlanePermutationAffineEquiv
open AlternatingFourBinaryActualPolynomialUniform (cycle)

private theorem cubic_two_seed_cover : ∀ i : Fin 4,
    ∃ j : Fin 2, ∃ m : Fin 3, (cycle ^ m.val) (![0,1] j) = i := by
  decide +kernel

variable {X : Type} [Finite X] {T : Subgroup (Equiv.Perm X)}
  (C : ProductBlockFrame T (Fin 4) Plane)

/-- The subgroup is the actual subgroup of the original top, with its
actual point action; no abstract cyclic action replaces it. -/
theorem cubic_subgroup_orbit_card_le_eight
    (P : Subgroup T) (g : P) (hg : C.top g.val = cycle) :
    Nat.card (MulAction.orbitRel.Quotient P X) ≤ 8 := by
  let labels : Fin 4 ≃ Plane :=
    (Finite.equivFinOfCardEq (by simp [Plane, Nat.card_eq_fintype_card])).symm
  let e : Fin 8 ≃ Fin 2 × Fin 4 :=
    (finProdFinEquiv : Fin 2 × Fin 4 ≃ Fin (2 * 4)).symm
  let rep : Fin 8 → X := fun j => C.frame (![0,1] (e j).1, labels (e j).2)
  have hcover (x : X) : ∃ j : Fin 8, x ∈ MulAction.orbit P (rep j) := by
    let z := C.frame.symm x
    obtain ⟨j,m,hm⟩ := cubic_two_seed_cover z.1
    let u : P := g ^ m.val
    let y := u⁻¹ • x
    let b := (C.frame.symm y).2
    have hy : (C.frame.symm y).1 = ![0,1] j := by
      have hh := C.intertwine (u⁻¹).val z
      rw [C.frame.apply_symm_apply] at hh
      change (C.frame.symm (u⁻¹ • x)).1 = C.top ((g.val ^ m.val)⁻¹) z.1 at hh
      rw [map_inv, map_pow, hg, ← hm] at hh
      simpa only [y, Equiv.Perm.inv_def, Equiv.symm_apply_apply] using hh
    have hb : C.frame (![0,1] j,b) = y := by
      apply C.frame.symm.injective
      rw [C.frame.symm_apply_apply]
      exact Prod.ext hy.symm rfl
    refine ⟨finProdFinEquiv (j,labels.symm b), u, ?_⟩
    change u • C.frame (![0,1] (e (finProdFinEquiv (j,labels.symm b))).1,
      labels (e (finProdFinEquiv (j,labels.symm b))).2) = x
    dsimp only [e]
    rw [Equiv.symm_apply_apply, Equiv.apply_symm_apply, hb]
    exact smul_inv_smul u x
  let orbitMap : Fin 8 → MulAction.orbitRel.Quotient P X :=
    fun j => Quotient.mk'' (rep j)
  have honto : Function.Surjective orbitMap := by
    intro q
    refine Quotient.inductionOn q ?_
    intro x
    obtain ⟨j,hj⟩ := hcover x
    exact ⟨j, (Quotient.sound ((MulAction.orbitRel_apply).mpr hj)).symm⟩
  simpa only [Nat.card_fin] using Nat.card_le_card_of_surjective orbitMap honto

end SymmetricSubgroupAsymptotics.ProductBlockFrame
