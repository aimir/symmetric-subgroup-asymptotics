import SymmetricSubgroupAsymptotics.BinaryPlaneFaithfulTopRegularLift
import SymmetricSubgroupAsymptotics.AlternatingFourBinaryActualPolynomialUniform

/-! The actual regular Klein range is contained in every nontrivial
normal subgroup of a faithful A4/S4 quartet image. Only displayed
permutation commutator and conjugacy identities are finite facts. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryPlaneFaithfulTopMonolith
open BinaryPlaneAlternatingKernelPartition (Frame)
open BinaryPlaneAlternatingCentralizerCommutators (R regular top)
open AlternatingFourBinaryActualPolynomialUniform (cycle)
local instance : Fintype R := BinaryRegularKleinWreath.rFintype
local instance : DecidableEq R := BinaryRegularKleinWreath.rDecidableEq

private theorem commutator_regular : ∀ p : Equiv.Perm (Fin 4), p≠1 →
    ∃ s : Equiv.Perm (Fin 4), s∈alternatingGroup (Fin 4) ∧
      ∃ r : R, p*s*p⁻¹*s⁻¹=regular r ∧ r≠1 := by
  change ∀ p : Equiv.Perm (Fin 4), p≠1 →
    ∃ s : Equiv.Perm (Fin 4), Equiv.Perm.sign s=1 ∧
      ∃ r : R, p*s*p⁻¹*s⁻¹=regular r ∧ r≠1
  decide +kernel

private theorem cycle_orbit : ∀ r : R, r≠1 → ∀ t : R,
    regular t=1 ∨ ∃ j : Fin 3,
      regular t=cycle^j.val*regular r*(cycle^j.val)⁻¹ := by decide +kernel

private theorem cycle_even : cycle∈alternatingGroup (Fin 4) := by
  change Equiv.Perm.sign cycle=1
  decide +kernel

theorem range_le_nontrivial_normal (C : Subgroup Frame)
    (hinj : Function.Injective (top C))
    (heven : ∀ p : alternatingGroup (Fin 4), ∃ h : C, (h : Frame).right=p.val)
    (l : R →* C) (ht : ∀ r, top C (l r)=regular r)
    (D : Subgroup C) (hD : D.Normal) (hDb : D≠⊥) : l.range≤D := by
  obtain ⟨g,hgn⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hDb
  have hp : top C (g : C)≠1 := by
    intro h
    apply hgn
    apply Subtype.ext
    apply hinj
    simpa only [map_one] using h
  obtain ⟨s,hs,r,hr,hrn⟩ := commutator_regular (top C (g : C)) hp
  obtain ⟨h,hh⟩ := heven ⟨s,hs⟩
  let x : C := (g : C)*h*(g : C)⁻¹*h⁻¹
  have hx : x∈D := by
    have hc := hD.conj_mem ((g : C)⁻¹) (D.inv_mem g.property) h
    simpa only [x,mul_assoc] using D.mul_mem g.property hc
  have hxt : top C x=regular r := by
    dsimp only [x]
    simp only [map_mul,map_inv]
    have hht : top C h=s := hh
    rw [hht]
    exact hr
  obtain ⟨a,ha⟩ := heven ⟨cycle,cycle_even⟩
  have hat : top C a=cycle := ha
  rintro z ⟨t,rfl⟩
  rcases cycle_orbit r hrn t with h | ⟨j,hj⟩
  · have he : l t=1 := hinj (by rw [ht,h,map_one])
    rw [he]
    exact D.one_mem
  · have he : l t=a^j.val*x*(a^j.val)⁻¹ := hinj (by
      simpa only [map_mul,map_inv,map_pow,ht,hxt,hat] using hj)
    rw [he]
    exact hD.conj_mem x hx (a^j.val)

end SymmetricSubgroupAsymptotics.BinaryPlaneFaithfulTopMonolith
