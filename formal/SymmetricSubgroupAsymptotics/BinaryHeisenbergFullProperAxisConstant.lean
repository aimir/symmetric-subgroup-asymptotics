import SymmetricSubgroupAsymptotics.BinaryHeisenbergCoordinateTemplate
import SymmetricSubgroupAsymptotics.RepresentationDisplacementSubgroup

/-! One actual proper-F axis. Only8 linear coordinates and the32 checked
original top rows are used; no normal subgroup lattice is enumerated. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
noncomputable section
open scoped Classical BigOperators
namespace SymmetricSubgroupAsymptotics.BinaryHeisenbergFullProperAxisConstant
open BinaryHeisenbergEightNaturalHeads
open BinaryRegularEightNaturalRegistry (chart1 chart23 chart45 chart33)

private def factorMasks : Fin 8 → ℕ := ![64,68,0,80,0,0,0,0]
private def factor : (Fin 1 → Fin 8 → ZMod 2) →ₗ[ZMod 2] V := {
  toFun := fun x i => ∑ j : Fin 8, (if (factorMasks i).testBit j.val then 1 else 0) * x 0 j
  map_add' := by intro x y; ext i; simp [mul_add, Finset.sum_add_distrib]
  map_smul' := by intro c x; ext i; simp [Finset.mul_sum, mul_left_comm] }

theorem full_space : chart1.space = ⊤ := by
  apply Submodule.eq_top_of_finrank_eq
  rw [chart1.finrank]
  simp

theorem fixed_iff (v : V) : v ∈ chart33.space ↔
    rho (generators 0) v - v ∈ chart23.space := by
  have h := binaryCoordinate_fixed_of_factor chart1 chart23 chart33 rho
    (fun _ : Fin 1 => generators 0) factor
    (by decide +kernel) (by decide +kernel) (by decide +kernel) v
  simpa only [full_space, Submodule.mem_top, true_and, Fin.forall_fin_one] using h

theorem fixed_card : Nat.card {v : V // rho (generators 0) v - v ∈ chart23.space} = 2 ^ 5 := by
  let e : {v : V // rho (generators 0) v - v ∈ chart23.space} ≃ chart33.space :=
    { toFun v := ⟨v.val, (fixed_iff v.val).mpr v.property⟩
      invFun v := ⟨v.val, (fixed_iff v.val).mp v.property⟩
      left_inv _ := rfl
      right_inv _ := rfl }
  exact (Nat.card_congr e).trans chart33.card

theorem carrier_stable (g : H) (v : V) (hv : v ∈ chart33.space) :
    rho g v ∈ chart33.space := by
  change rho g v ∈ (states 13).toSubmodule
  exact (states 13).apply_mem_toSubmodule g hv

theorem carrier_le_body : chart33.space ≤ chart45.space :=
  chart33.le_of_basis_mem _ (by decide +kernel)

theorem body_displacement (g : H) (v : V) (hv : v ∈ chart45.space) :
    rho g v - v ∈ chart33.space := by
  apply representation_displacement_mem_of_actual_generators rho (states 12)
    chart33.space generators generators_full _ g v hv
  intro j x hx
  let L : V →ₗ[ZMod 2] V := rho (generators j) - LinearMap.id
  have hle : chart45.space ≤ chart33.space.comap L :=
    chart45.le_of_basis_mem _ (fun i => by
      change rho (generators j) (chart45.inclusion (Pi.single i 1)) -
        chart45.inclusion (Pi.single i 1) ∈ chart33.space
      have hb : ∀ j : Fin 5, ∀ i : Fin 7,
        rho (generators j) (chart45.inclusion (Pi.single i 1)) -
          chart45.inclusion (Pi.single i 1) ∈ chart33.space := by decide +kernel
      exact hb j i)
  exact hle hx

theorem central_displacement (v : V) : rho (generators 0) v - v ∈ chart33.space := by
  let L : V →ₗ[ZMod 2] V := rho (generators 0) - LinearMap.id
  have hle : chart1.space ≤ chart33.space.comap L :=
    chart1.le_of_basis_mem _ (fun i => by
      change rho (generators 0) (chart1.inclusion (Pi.single i 1)) -
        chart1.inclusion (Pi.single i 1) ∈ chart33.space
      have hb : ∀ i : Fin 8, rho (generators 0) (chart1.inclusion (Pi.single i 1)) -
        chart1.inclusion (Pi.single i 1) ∈ chart33.space := by decide +kernel
      exact hb i)
  exact hle (full_space.symm ▸ Submodule.mem_top)

theorem top_card : Nat.card {t : H // ∀ v, v ∈ chart45.space →
    rho t v - v ∈ chart23.space} ≤ 1 :=
  BinaryHeisenbergCoordinateTemplate.top_card_le chart45 chart23 1 (by decide +kernel)

end SymmetricSubgroupAsymptotics.BinaryHeisenbergFullProperAxisConstant
