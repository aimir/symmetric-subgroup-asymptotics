import SymmetricSubgroupAsymptotics.CFSGCentralCocyclePGroup
import Mathlib.GroupTheory.Abelianization.Defs

/-! Derived fixed elements admit actual fixed lifts through a central
quotient. Arbitrary fixed elements need not lift fixed, and the kernel
need not be fixed pointwise. The central difference homomorphism kills
the commutator of the full preimage of the fixed target. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGCentralTwistedCommutatorLift
variable {G Q : Type*} [Group G] [Group Q]

def fixedSubgroup (tau : MulAut G) : Subgroup G where
  carrier := {x | tau x = x}
  one_mem' := map_one tau
  mul_mem' := by
    intro x y hx hy
    change tau (x * y) = x * y
    change tau x = x at hx
    change tau y = y at hy
    rw [map_mul, hx, hy]
  inv_mem' := by
    intro x hx
    change tau x⁻¹ = x⁻¹
    change tau x = x at hx
    rw [map_inv, hx]

theorem exists_fixed_lift_of_mem_commutator_fixed (f : G →* Q)
    (hf : Function.Surjective f) (hker : f.ker ≤ Subgroup.center G)
    (alpha : MulAut G) (beta : MulAut Q)
    (hcov : ∀ x, f (alpha x) = beta (f x))
    (z : fixedSubgroup beta) (hz : z ∈ commutator (fixedSubgroup beta)) :
    ∃ v : G, alpha v = v ∧ f v = z.val := by
  let L := (fixedSubgroup beta).comap f
  let fL : L →* fixedSubgroup beta :=
    (f.comp L.subtype).codRestrict (fixedSubgroup beta) (fun x => x.property)
  have hfL : Function.Surjective fL := by
    intro y
    obtain ⟨x, hx⟩ := hf y.val
    have hxL : x ∈ L := by
      change f x ∈ fixedSubgroup beta
      rw [hx]
      exact y.property
    exact ⟨⟨x, hxL⟩, Subtype.ext hx⟩
  have hcentral (x : L) : x.val⁻¹ * alpha x.val ∈ Subgroup.center G := by
    apply hker
    change f (x.val⁻¹ * alpha x.val) = 1
    rw [map_mul, map_inv, hcov]
    have hx : beta (f x.val) = f x.val := x.property
    rw [hx, inv_mul_cancel]
  letI : CommGroup (Subgroup.center G) :=
    { (inferInstance : Group (Subgroup.center G)) with
      mul_comm := fun a b => Subtype.ext ((Subgroup.mem_center_iff.mp a.property) b.val).symm }
  let c : L →* Subgroup.center G := CFSGCentralCocyclePGroup.centralDifferenceHom alpha L hcentral
  have hc : commutator L ≤ c.ker := Abelianization.commutator_subset_ker c
  have hmap : (commutator L).map fL = commutator (fixedSubgroup beta) := by
    simp only [commutator_def, Subgroup.map_commutator, Subgroup.map_top_of_surjective fL hfL]
  rw [← hmap] at hz
  obtain ⟨v, hv, hvz⟩ := hz
  have hcv : c v = 1 := hc hv
  have hdiff : v.val⁻¹ * alpha v.val = 1 := congrArg Subtype.val hcv
  exact ⟨v.val, (inv_mul_eq_one.mp hdiff).symm, congrArg Subtype.val hvz⟩

end SymmetricSubgroupAsymptotics.CFSGCentralTwistedCommutatorLift
