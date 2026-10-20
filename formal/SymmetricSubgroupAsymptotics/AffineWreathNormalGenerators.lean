import SymmetricSubgroupAsymptotics.AffineWreathSimpleComplementNormalGenerators

/-! A positive uniform normal-generator bound on the wreath of the actual
linear complement lifts to its irreducible affine wreath unchanged. -/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics
namespace AffineModel

open SemidirectProduct

variable {p d : ℕ} [Fact p.Prime] (R : Subgroup (GLV p d)) [Nontrivial R]

theorem wreath_normal_generating_tuples
    (hirr : Irreducible R) (v : V p d) (hv : v ≠ 0)
    {t : ℕ} (ht : 0 < t)
    (hR : ∀ N : Subgroup (C2Wreath.W R), N.Normal →
      ∃ x : Fin t → C2Wreath.W R, Subgroup.normalClosure (Set.range x) = N) :
    ∀ N : Subgroup (C2Wreath.W (Aff R)), N.Normal →
      ∃ x : Fin t → C2Wreath.W (Aff R), Subgroup.normalClosure (Set.range x) = N := by
  letI : Nontrivial (Aff R) :=
    ⟨⟨inl (Multiplicative.ofAdd v), 1, inl_ofAdd_ne_one R hv⟩⟩
  apply C2Wreath.normal_generating_tuples_of_local_normal_cover
    (rightHom : Aff R →* R) rightHom_surjective
    (center_eq_bot_of_irreducible R hirr) ?_ ?_ ht hR
  · rw [← range_inl_eq_ker_rightHom]
    exact Vsub_ne_bot_of_nonzero R hv
  · intro K hK hKb
    letI := hK
    rw [← range_inl_eq_ker_rightHom]
    exact Vsub_le_normal hirr K hKb

end AffineModel
end SymmetricSubgroupAsymptotics

end
