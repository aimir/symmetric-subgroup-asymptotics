import SymmetricSubgroupAsymptotics.PrimeRelativeCharacterKernel
import SymmetricSubgroupAsymptotics.PrimeDerivedIntersectionImage

/-! Exact quotient-center detection for the literal kernel of an original
invariant derived character. The same original evaluation and commutator
form occur on both sides. Containment of the original derived group in the
center preimage is proved before taking its quotient. -/
set_option autoImplicit false
noncomputable section
open scoped commutatorElement

namespace SymmetricSubgroupAsymptotics

variable (p : ℕ) [Fact p.Prime] {G : Type*} [Group G] [Finite G]
variable (hker : (primeAbelianizationGroupMap p G).ker = commutator G)
include hker

/-- Centrality modulo the actual character kernel is exactly membership
in the radical of the same character's actual commutator form. -/
theorem mem_quotientCenterPreimage_characterKernel_iff
    (χ : primeRelativeCharacters p (commutator G)) (x : G) :
    x ∈ quotientCenterPreimage (primeRelativeCharacterKernel p (commutator G) χ) ↔
      primeAbelianizationMap p G (Additive.ofMul x) ∈
        (derivedEvaluationBilinearMap p hker χ).ker := by
  rw [mem_quotientCenterPreimage_iff_all_commutators]
  constructor
  · intro hx
    change derivedEvaluationBilinear p hker χ
      (primeAbelianizationMap p G (Additive.ofMul x)) = 0
    apply LinearMap.ext
    intro v
    obtain ⟨y, rfl⟩ := primeAbelianizationMap_surjective p G v
    change derivedEvaluationBilinear p hker χ
      (primeAbelianizationMap p G (Additive.ofMul x))
      (primeAbelianizationMap p G (Additive.ofMul y.toMul)) = 0
    rw [derivedEvaluationBilinear_eval]
    exact (coe_mem_primeRelativeCharacterKernel_iff p (commutator G) χ
      (derivedCommutatorElement x y.toMul)).mp (hx y.toMul)
  · intro hx y
    apply (coe_mem_primeRelativeCharacterKernel_iff p (commutator G) χ
      (derivedCommutatorElement x y)).mpr
    have h := LinearMap.congr_fun
      (show derivedEvaluationBilinear p hker χ
        (primeAbelianizationMap p G (Additive.ofMul x)) = 0 from hx)
      (primeAbelianizationMap p G (Additive.ofMul y))
    rw [derivedEvaluationBilinear_eval] at h
    exact h

theorem commutator_le_quotientCenterPreimage_characterKernel
    (χ : primeRelativeCharacters p (commutator G)) :
    commutator G ≤ quotientCenterPreimage (primeRelativeCharacterKernel p (commutator G) χ) := by
  intro x hx
  apply (mem_quotientCenterPreimage_characterKernel_iff p hker χ x).mpr
  have hz : primeAbelianizationMap p G (Additive.ofMul x) = 0 := by
    have hm : x ∈ (primeAbelianizationGroupMap p G).ker := by rwa [hker]
    exact hm
  rw [hz]
  exact Submodule.zero_mem _

/-- This is an equality of actual images, so every form-radical vector
has an original central-mod-kernel representative. -/
theorem primeDerivedImage_quotientCenterPreimage_characterKernel
    (χ : primeRelativeCharacters p (commutator G)) :
    primeDerivedImage p (quotientCenterPreimage
      (primeRelativeCharacterKernel p (commutator G) χ)) =
      (derivedEvaluationBilinearMap p hker χ).ker := by
  apply le_antisymm
  · intro v hv
    obtain ⟨x, rfl⟩ := (mem_primeDerivedImage_iff p _ v).mp hv
    exact (mem_quotientCenterPreimage_characterKernel_iff p hker χ x).mp x.2
  · intro v hv
    obtain ⟨x, rfl⟩ := primeAbelianizationMap_surjective p G v
    apply (mem_primeDerivedImage_iff p _ _).mpr
    exact ⟨⟨x.toMul,
      (mem_quotientCenterPreimage_characterKernel_iff p hker χ x.toMul).mpr hv⟩, rfl⟩

/-- The original quotient image is equivalent to the literal form radical.
The preceding containment theorem makes this the quotient of the center
preimage by the original derived group. -/
def derivedCharacterKernelCenterEquiv
    (χ : primeRelativeCharacters p (commutator G)) :
    normalChainQuotient (commutator G)
      (quotientCenterPreimage (primeRelativeCharacterKernel p (commutator G) χ)) ≃*
      Multiplicative (derivedEvaluationBilinearMap p hker χ).ker :=
  (derivedNormalImageEquiv p hker
    (quotientCenterPreimage (primeRelativeCharacterKernel p (commutator G) χ))).trans
    (LinearEquiv.ofEq _ _
      (primeDerivedImage_quotientCenterPreimage_characterKernel p hker χ)).toAddEquiv.toMultiplicative

/-- The exact center-preimage order retains the original derived-group
order and the exact radical of the same original character form. -/
theorem quotientCenterPreimage_characterKernel_card
    (χ : primeRelativeCharacters p (commutator G)) :
    Nat.card (quotientCenterPreimage (primeRelativeCharacterKernel p (commutator G) χ)) =
      p ^ Module.finrank (ZMod p) (derivedEvaluationBilinearMap p hker χ).ker *
        Nat.card (commutator G) := by
  have h := primeDerivedImage_pow_finrank_mul_intersection p hker
    (quotientCenterPreimage (primeRelativeCharacterKernel p (commutator G) χ))
  rw [primeDerivedImage_quotientCenterPreimage_characterKernel p hker χ,
    inf_eq_right.mpr (commutator_le_quotientCenterPreimage_characterKernel p hker χ)] at h
  exact h.symm

end SymmetricSubgroupAsymptotics
