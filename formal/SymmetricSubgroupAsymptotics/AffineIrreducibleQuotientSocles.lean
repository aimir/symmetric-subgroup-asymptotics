import SymmetricSubgroupAsymptotics.AffineIrreducibleNormalGenerators
import SymmetricSubgroupAsymptotics.NormalCoverQuotientSocles

/-! A faithful irreducible affine group inherits the all-quotient socle
bound of its complement. Unlike an all-normal-generator theorem, this
requires no normal-chain property or bound on arbitrary complement normals.
The actual right projection and every original quotient map are retained. -/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics.AffineModel

open SemidirectProduct

variable {p d : ℕ} [Fact p.Prime] (R : Subgroup (GLV p d))

theorem socle_of_surjective_of_irreducible_complement_quotients
    (hirr : Irreducible R) (v : V p d) (hv : v ≠ 0)
    {t : ℕ} (ht : 1 ≤ t)
    (hR : ∀ N : Subgroup R, ∀ _ : N.Normal,
      SocleNormalGeneratorBound (R ⧸ N) t)
    {Q : Type} [Group Q] (pi : Aff R →* Q) (hpi : Function.Surjective pi) :
    SocleNormalGeneratorBound Q t := by
  apply quotientSocle_of_surjective_normal_cover
    (rightHom : Aff R →* R) rightHom_surjective _ _ ht hR pi hpi
  · rw [← range_inl_eq_ker_rightHom]
    exact Vsub_ne_bot_of_nonzero R hv
  · intro N hN hNb
    letI := hN
    rw [← range_inl_eq_ker_rightHom]
    exact Vsub_le_normal hirr N hNb

theorem quotientSocle_of_irreducible_complement_quotients
    (hirr : Irreducible R) (v : V p d) (hv : v ≠ 0)
    {t : ℕ} (ht : 1 ≤ t)
    (hR : ∀ M : Subgroup R, ∀ _ : M.Normal,
      SocleNormalGeneratorBound (R ⧸ M) t)
    (N : Subgroup (Aff R)) [N.Normal] : SocleNormalGeneratorBound (Aff R ⧸ N) t :=
  socle_of_surjective_of_irreducible_complement_quotients R hirr v hv ht hR
    (QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N)

/-- The unrestricted numerical form is the maximum of one and the
complement's all-quotient bound. -/
theorem socle_of_surjective_of_irreducible_complement_quotients_max
    (hirr : Irreducible R) (v : V p d) (hv : v ≠ 0)
    {t : ℕ}
    (hR : ∀ N : Subgroup R, ∀ _ : N.Normal,
      SocleNormalGeneratorBound (R ⧸ N) t)
    {Q : Type} [Group Q] (pi : Aff R →* Q) (hpi : Function.Surjective pi) :
    SocleNormalGeneratorBound Q (max 1 t) :=
  socle_of_surjective_of_irreducible_complement_quotients R hirr v hv (le_max_left _ _)
    (fun N hN => (hR N hN).mono (le_max_right _ _)) pi hpi

end SymmetricSubgroupAsymptotics.AffineModel

end
