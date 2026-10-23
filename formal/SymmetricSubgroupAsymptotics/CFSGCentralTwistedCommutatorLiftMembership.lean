import SymmetricSubgroupAsymptotics.CFSGCentralTwistedCommutatorLift

/-! Fixed lifts retain membership in the commutator of the full preimage
of the fixed target. This is stronger than mere existence of a fixed
lift and does not assert surjectivity on arbitrary fixed points. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGCentralTwistedCommutatorLift
variable {G Q : Type*} [Group G] [Group Q]

def fixedPreimage (f : G →* Q) (beta : MulAut Q) : Subgroup G :=
  (fixedSubgroup beta).comap f

theorem preimage_commutator_fixed (f : G →* Q)
    (hker : f.ker ≤ Subgroup.center G) (alpha : MulAut G) (beta : MulAut Q)
    (hcov : ∀ x, f (alpha x) = beta (f x))
    (v : fixedPreimage f beta) (hv : v ∈ commutator (fixedPreimage f beta)) :
    alpha v.val = v.val := by
  let L := fixedPreimage f beta
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
  have hdiff : v.val⁻¹ * alpha v.val = 1 := congrArg Subtype.val (hc hv)
  exact (inv_mul_eq_one.mp hdiff).symm

theorem exists_fixed_lift_in_preimage_commutator (f : G →* Q)
    (hf : Function.Surjective f) (hker : f.ker ≤ Subgroup.center G)
    (alpha : MulAut G) (beta : MulAut Q)
    (hcov : ∀ x, f (alpha x) = beta (f x))
    (z : fixedSubgroup beta) (hz : z ∈ commutator (fixedSubgroup beta)) :
    ∃ v : fixedPreimage f beta, v ∈ commutator (fixedPreimage f beta) ∧
      alpha v.val = v.val ∧ f v.val = z.val := by
  let L := fixedPreimage f beta
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
  have hmap : (commutator L).map fL = commutator (fixedSubgroup beta) := by
    simp only [commutator_def, Subgroup.map_commutator, Subgroup.map_top_of_surjective fL hfL]
  rw [← hmap] at hz
  obtain ⟨v, hv, hvz⟩ := hz
  exact ⟨v, hv, preimage_commutator_fixed f hker alpha beta hcov v hv,
    congrArg Subtype.val hvz⟩

end SymmetricSubgroupAsymptotics.CFSGCentralTwistedCommutatorLift
