import SymmetricSubgroupAsymptotics.PrimeDerivedJointHead
import SymmetricSubgroupAsymptotics.StarAlternatingHead

/-! The original above-derived head bound for a genuine star-form
coordinate model. The only model inputs are two linear equivalences and
the pointwise identity for the actual commutator forms. Neither a normal
subgroup menu nor a numerical head bound is an input. -/
set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics

variable (p : ℕ) [Fact p.Prime]
    {G : Type*} [Group G] [Finite G]
    (hker : (primeAbelianizationGroupMap p G).ker = commutator G)
    {U : Type*} [AddCommGroup U] [Module (ZMod p) U] [FiniteDimensional (ZMod p) U]

/-- Every original normal above G' obeys the star-family head bound,
once the complete actual character and evaluation coordinates are bound. -/
theorem primeRelativeHead_above_derived_le_max_of_star
    (eChars : primeRelativeCharacters p (commutator G) ≃ₗ[ZMod p]
      Module.Dual (ZMod p) U)
    (eV : PrimeAbelianization p G ≃ₗ[ZMod p] U × ZMod p)
    (hform : ∀ χ x y, derivedEvaluationBilinearMap p hker χ x y =
      starAlternatingFamily (eChars χ) (eV x) (eV y))
    (N : Subgroup G) [N.Normal] (hDN : commutator G ≤ N) :
    Module.finrank (ZMod p) (primeRelativeCharacters p N) ≤
      max (Module.finrank (ZMod p) U)
        (Module.finrank (ZMod p) (primeDerivedImage p N)) :=
  (primeRelativeHead_above_derived_le_image_add_joint p hker N hDN).trans
    (linearJointAnnihilator_finrank_add_le_max_of_star
      (derivedEvaluationBilinearMap p hker) eChars eV hform (primeDerivedImage p N))

/-- Exact original quotient-cardinality form of the same bound. -/
theorem primeRelativeHead_above_derived_le_max_log_of_star
    (eChars : primeRelativeCharacters p (commutator G) ≃ₗ[ZMod p]
      Module.Dual (ZMod p) U)
    (eV : PrimeAbelianization p G ≃ₗ[ZMod p] U × ZMod p)
    (hform : ∀ χ x y, derivedEvaluationBilinearMap p hker χ x y =
      starAlternatingFamily (eChars χ) (eV x) (eV y))
    (N : Subgroup G) [N.Normal] (hDN : commutator G ≤ N) :
    Module.finrank (ZMod p) (primeRelativeCharacters p N) ≤
      max (Module.finrank (ZMod p) U)
        (Nat.log p (Nat.card (normalChainQuotient (commutator G) N))) := by
  rw [derivedNormalImage_log_card p hker N]
  exact primeRelativeHead_above_derived_le_max_of_star p hker eChars eV hform N hDN

end SymmetricSubgroupAsymptotics
