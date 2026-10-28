import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.GroupTheory.Subgroup.Centralizer
import Mathlib.Algebra.Group.Subgroup.Pointwise
import Mathlib.Tactic.Group

set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.PointStabilizerJoinOrbitReturn
open MulAction

theorem normalizes_join_of_orbit_return {G X : Type*} [Group G] [MulAction G X]
    (P Z : Subgroup G) (hZC : Z ≤ Subgroup.centralizer (P : Set G))
    (t : G) (htP : t ∈ Subgroup.normalizer (P : Set G))
    (htZ : t ∈ Subgroup.normalizer (Z : Set G)) (x : X)
    (hPF : P ≤ Subgroup.normalizer
      (((P ⊓ stabilizer G x) ⊔ Z : Subgroup G) : Set G))
    (hreturn : t • x ∈ orbit P x) :
    t ∈ Subgroup.normalizer (((P ⊓ stabilizer G x) ⊔ Z : Subgroup G) : Set G) := by
  obtain ⟨r, hr⟩ := hreturn
  let k : G := (r : G)⁻¹ * t
  have hPNZ : P ≤ Subgroup.normalizer (Z : Set G) :=
    (Subgroup.le_centralizer_iff.mp hZC).trans (Subgroup.centralizer_le_normalizer _)
  have hkP : k ∈ Subgroup.normalizer (P : Set G) :=
    (Subgroup.normalizer (P : Set G)).mul_mem
      ((Subgroup.normalizer (P : Set G)).inv_mem (P.le_normalizer r.property)) htP
  have hkZ : k ∈ Subgroup.normalizer (Z : Set G) :=
    (Subgroup.normalizer (Z : Set G)).mul_mem
      ((Subgroup.normalizer (Z : Set G)).inv_mem (hPNZ r.property)) htZ
  have hkfix : k ∈ stabilizer G x := by
    change ((r : G)⁻¹ * t) • x = x
    rw [mul_smul, ← hr]
    exact inv_smul_smul (r : G) x
  have hkU : k ∈ Subgroup.normalizer ((P ⊓ stabilizer G x : Subgroup G) : Set G) :=
    Subgroup.inf_normalizer_le_normalizer_inf
      ⟨hkP, (stabilizer G x).le_normalizer hkfix⟩
  have hkF := ((P ⊓ stabilizer G x).normalizer_inf_normalizer_le_normalizer_sup Z)
    ⟨hkU, hkZ⟩
  have he : (r : G) * k = t := by dsimp [k]; group
  exact he ▸ (Subgroup.normalizer
    (((P ⊓ stabilizer G x) ⊔ Z : Subgroup G) : Set G)).mul_mem (hPF r.property) hkF

end SymmetricSubgroupAsymptotics.PointStabilizerJoinOrbitReturn
