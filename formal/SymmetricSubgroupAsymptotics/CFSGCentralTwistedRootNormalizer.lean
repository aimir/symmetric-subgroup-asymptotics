import SymmetricSubgroupAsymptotics.CFSGCentralTwistedCommutatorLift
import Mathlib.Tactic.Group

/-! Conjugation by a centrally twisted element preserves genuinely
fixed root subgroups when it normalizes the underlying root groups.
Centrality is relative to the containing group, not to a matrix algebra. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGCentralTwistedRootNormalizer
open CFSGCentralTwistedCommutatorLift
variable {G : Type*} [Group G]

def fixedGenerated (tau : MulAut G) (U V : Subgroup G) : Subgroup G :=
  (U ⊓ fixedSubgroup tau) ⊔ (V ⊓ fixedSubgroup tau)

theorem conjugate_fixed_of_central_twist (tau : MulAut G) (H : Subgroup G)
    (d u : G) (hd : d ∈ H) (hu : u ∈ H) (hfixed : tau u = u)
    (hcentral : ∀ x ∈ H, (tau d*d⁻¹)*x = x*(tau d*d⁻¹)) :
    tau (d*u*d⁻¹) = d*u*d⁻¹ := by
  let c := tau d*d⁻¹
  have htd : tau d = c*d := by
    dsimp only [c]
    rw [inv_mul_cancel_right]
  have hconj : d*u*d⁻¹ ∈ H := H.mul_mem (H.mul_mem hd hu) (H.inv_mem hd)
  have hc : c*(d*u*d⁻¹) = (d*u*d⁻¹)*c := hcentral _ hconj
  calc
    tau (d*u*d⁻¹) = tau d*u*(tau d)⁻¹ := by rw [map_mul,map_mul,map_inv,hfixed]
    _ = c*(d*u*d⁻¹)*c⁻¹ := by rw [htd]; group
    _ = d*u*d⁻¹ := by rw [hc,mul_assoc,mul_inv_cancel,mul_one]

theorem central_twisted_normalizes_fixed_generated (tau : MulAut G)
    (H U V D L : Subgroup G) (hU : U ≤ H) (hV : V ≤ H) (hL : L ≤ H)
    (hDU : D ≤ Subgroup.normalizer (U : Set G))
    (hDV : D ≤ Subgroup.normalizer (V : Set G))
    (hcentral : ∀ d ∈ L, ∀ x ∈ H, (tau d*d⁻¹)*x = x*(tau d*d⁻¹)) :
    D ⊓ L ≤ Subgroup.normalizer (fixedGenerated tau U V : Set G) := by
  apply Subgroup.le_normalizer_iff.mpr
  intro d hd x hx
  have hmap (P : Subgroup G) (hPH : P ≤ H)
      (hDP : D ≤ Subgroup.normalizer (P : Set G))
      (hPJ : P ⊓ fixedSubgroup tau ≤ fixedGenerated tau U V) :
      P ⊓ fixedSubgroup tau ≤ (fixedGenerated tau U V).comap (MulAut.conj d).toMonoidHom := by
    intro u hu
    have hp : d*u*d⁻¹ ∈ P := (Subgroup.mem_normalizer_iff.mp (hDP hd.1) u).mp hu.1
    have hf : tau (d*u*d⁻¹) = d*u*d⁻¹ :=
      conjugate_fixed_of_central_twist tau H d u (hL hd.2) (hPH hu.1) hu.2
        (hcentral d hd.2)
    exact hPJ ⟨hp,hf⟩
  exact (sup_le (hmap U hU hDU le_sup_left) (hmap V hV hDV le_sup_right)) hx

end SymmetricSubgroupAsymptotics.CFSGCentralTwistedRootNormalizer
