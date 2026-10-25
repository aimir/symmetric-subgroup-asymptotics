import SymmetricSubgroupAsymptotics.CentralExtensionScalarPairingIndex
import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.GroupTheory.Subgroup.Center

/-! Nondegeneracy identifies the entire centre of an actual scalar
central extension. This uses the given commutator, not recognition. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CentralExtensionScalarPairingCentre
open scoped commutatorElement
open CentralExtensionScalarPairingIndex
variable {F V N : Type*} [Field F] [AddCommGroup V] [Module F V] [Group N]

theorem central_range_le_center (D : Data (F := F) (V := V) (N := N)) :
    D.central.range ≤ Subgroup.center N := by
  rintro z ⟨a,rfl⟩
  have hp : D.projection (D.central a) = 1 :=
    D.central_range.le ⟨a,rfl⟩
  apply Subgroup.mem_center_iff.mpr
  intro y
  have hc := D.commutator (D.central a) y
  rw [hp] at hc
  have hz : D.pairing (0 : V) (D.projection y).toAdd = 0 := by
    simp only [map_zero,LinearMap.zero_apply]
  change D.central a*y*(D.central a)⁻¹*y⁻¹ =
    D.central (Multiplicative.ofAdd (D.pairing 0 (D.projection y).toAdd)) at hc
  rw [hz] at hc
  have hc1 : ⁅D.central a,y⁆ = 1 := hc.trans (map_one D.central)
  exact ((commutatorElement_eq_one_iff_mul_comm).mp hc1).symm

theorem center_eq_central_range (D : Data (F := F) (V := V) (N := N)) :
    Subgroup.center N = D.central.range := by
  apply le_antisymm _ (central_range_le_center D)
  intro x hx
  apply D.central_range.symm.le
  change D.projection x = 1
  by_contra hp
  have hv : (D.projection x).toAdd ≠ 0 := hp
  obtain ⟨v,hv1⟩ := D.full _ hv (1 : F)
  obtain ⟨y,hy⟩ := D.projection_surjective (Multiplicative.ofAdd v)
  have hc := D.commutator x y
  rw [hy] at hc
  have hcomm : x*y*x⁻¹*y⁻¹ = 1 :=
    commutatorElement_eq_one_iff_mul_comm.mpr ((Subgroup.mem_center_iff.mp hx y).symm)
  rw [hcomm] at hc
  have he : (1 : Multiplicative F) = Multiplicative.ofAdd (1 : F) := by
    apply D.central_injective
    exact (map_one D.central).trans (hc.trans (congrArg D.central (congrArg Multiplicative.ofAdd hv1)))
  have hf : (0 : F) = 1 := congrArg Multiplicative.toAdd he
  exact zero_ne_one hf

def centralEquiv (D : Data (F := F) (V := V) (N := N)) :
    Multiplicative F ≃* Subgroup.center N :=
  (MonoidHom.ofInjective D.central_injective).trans
    (MulEquiv.subgroupCongr (center_eq_central_range D).symm)

theorem centralEquiv_val (D : Data (F := F) (V := V) (N := N))
    (a : Multiplicative F) : (centralEquiv D a).val = D.central a := rfl

end SymmetricSubgroupAsymptotics.CentralExtensionScalarPairingCentre
