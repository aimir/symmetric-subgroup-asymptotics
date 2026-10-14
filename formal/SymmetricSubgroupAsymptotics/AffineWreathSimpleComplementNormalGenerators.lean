import SymmetricSubgroupAsymptotics.C2WreathNormalCoverQuotient
import SymmetricSubgroupAsymptotics.AffineSimpleComplementNormalChain

/-! An irreducible affine group with centerless simple complement has a
two-block wreath product whose normal subgroups each have one normal
generator. The translations are the exact kernel of the local projection. -/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics
namespace AffineModel

open SemidirectProduct

variable {p d : ℕ} [Fact p.Prime] (R : Subgroup (GLV p d))

theorem center_eq_bot_of_irreducible [Nontrivial R] (hirr : Irreducible R) :
    Subgroup.center (Aff R) = ⊥ := by
  by_contra hcenter
  have hV := Vsub_le_normal hirr (Subgroup.center (Aff R)) hcenter
  obtain ⟨r, hr⟩ := exists_ne (1 : R)
  apply hr
  apply Subtype.ext
  apply LinearEquiv.ext
  intro v
  have h := Subgroup.mem_center_iff.mp
    (hV (show (inl (Multiplicative.ofAdd v) : Aff R) ∈ Vsub R from ⟨_, rfl⟩))
    (inr r)
  have hv := congrArg (fun g : Aff R ↦ g.left.toAdd) h
  change 0 + (r : GLV p d) v = v + (1 : GLV p d) 0 at hv
  simpa only [map_zero, add_zero, zero_add] using hv

theorem wreath_normal_generating_singletons [IsSimpleGroup R]
    (hirr : Irreducible R) (hcenter : Subgroup.center R = ⊥)
    (v : V p d) (hv : v ≠ 0) :
    ∀ N : Subgroup (C2Wreath.W (Aff R)), N.Normal →
      ∃ x : Fin 1 → C2Wreath.W (Aff R), Subgroup.normalClosure (Set.range x) = N := by
  letI : Nontrivial (Aff R) :=
    ⟨⟨inl (Multiplicative.ofAdd v), 1, inl_ofAdd_ne_one R hv⟩⟩
  apply C2Wreath.normal_generating_tuples_of_local_normal_cover
    (rightHom : Aff R →* R) rightHom_surjective
    (center_eq_bot_of_irreducible R hirr) ?_ ?_ (by decide)
    (C2Wreath.normal_generating_singletons_of_simple hcenter)
  · rw [← range_inl_eq_ker_rightHom]
    exact Vsub_ne_bot_of_nonzero R hv
  · intro K hK hKb
    letI := hK
    rw [← range_inl_eq_ker_rightHom]
    exact Vsub_le_normal hirr K hKb

end AffineModel
end SymmetricSubgroupAsymptotics

end
