import SymmetricSubgroupAsymptotics.BinarySplitElementary16PhiZeroStabilizerData

/-! Structural use of separately checked finite stabilizer facts. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.BinarySplitElementary16PhiZeroStabilizer
local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

private theorem kill_state (i : Fin 16) (v : V) (hv : v ∈ state.space) :
    rowAction i v - v ∈ radical.space := by
  have h : v ∈ radical.space.comap ((rowAction i : V →ₗ[ZMod 2] V) - (LinearMap.id : V →ₗ[ZMod 2] V)) :=
    (state.le_of_basis_mem (radical.space.comap ((rowAction i : V →ₗ[ZMod 2] V) - (LinearMap.id : V →ₗ[ZMod 2] V))) (fun j => by
      change ((rowAction i : V →ₗ[ZMod 2] V) - (LinearMap.id : V →ₗ[ZMod 2] V)) (state.inclusion (Pi.single j 1)) ∈ radical.space
      simpa only [LinearMap.sub_apply, LinearMap.id_apply] using kill_basis i j)) hv
  change ((rowAction i : V →ₗ[ZMod 2] V) - (LinearMap.id : V →ₗ[ZMod 2] V)) v ∈ radical.space at h
  simpa only [LinearMap.sub_apply, LinearMap.id_apply] using h
theorem count_bound (v : V) (hv : v ∉ state.space) :
    Nat.card {i : Fin 16 // rowAction i v - v ∈ radical.space} ≤ 2 :=
  linear_stabilizer_count_le_of_quotient_representatives rowAction state.space radical.space projection sectionMap
    (linear_quotient_defect_mem_of_basis state.space projection sectionMap quotient_basis)
    kill_state 2 section_count v hv

/-- Once the full original model supplies its bijective rows and their
literal affine action, the same original fixed kernel lies in this state. -/
theorem kernel_le {H : Type} [Group H] (row : Fin 16 → H)
    (hrow : Function.Bijective row) (rho : Representation (ZMod 2) H V)
    (hact : ∀ i, rho (row i) = rowAction i)
    (D : Subgroup H) (hD : 2 < Nat.card D) (K : Submodule (ZMod 2) V)
    (hfixed : ∀ d : D, ∀ v ∈ K, rho (d : H) v - v ∈ radical.space) :
    K ≤ state.space := by
  apply submodule_le_of_small_stabilizer_rows row hrow rho state.space radical.space K 2
    _ D hD hfixed
  intro v hv
  simpa only [hact] using count_bound v hv

end SymmetricSubgroupAsymptotics.BinarySplitElementary16PhiZeroStabilizer
