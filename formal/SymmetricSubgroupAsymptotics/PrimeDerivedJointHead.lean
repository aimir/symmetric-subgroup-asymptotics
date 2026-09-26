import SymmetricSubgroupAsymptotics.PrimeDerivedEvaluationPairing
import SymmetricSubgroupAsymptotics.LinearJointAnnihilator

/-! Uniform original-normal head bounds above G' from the actual family
of alternating commutator forms. The subspace W is the actual evaluation
image of N; no normal-subgroup list or subspace enumeration is an input.
Only the stated single/pair kernel bounds on those actual forms remain
for a finite coordinate certificate to discharge.
-/
set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics

variable (p : ℕ) [Fact p.Prime]
variable {G : Type*} [Group G] [Finite G]
variable (hker : (primeAbelianizationGroupMap p G).ker = commutator G)

/-- The literal normal-chain image in G/G' is equivalent to the actual
evaluation image W, with the same underlying original elements. -/
def derivedNormalImageEquiv (N : Subgroup G) [N.Normal] :
    normalChainQuotient (commutator G) N ≃* Multiplicative (primeDerivedImage p N) where
  toFun x := Multiplicative.ofAdd
    ⟨(derivedAbelianizationEquiv p hker x.1).toAdd, by
      apply (mem_primeDerivedImage_iff p N _).mpr
      obtain ⟨g, hg, hgq⟩ := x.2
      refine ⟨⟨g, hg⟩, ?_⟩
      rw [← hgq]
      rfl⟩
  invFun w := ⟨(derivedAbelianizationEquiv p hker).symm
      (Multiplicative.ofAdd w.toAdd.1), by
    obtain ⟨n, hn⟩ := (mem_primeDerivedImage_iff p N _).mp w.toAdd.2
    refine ⟨(n : G), n.2, ?_⟩
    apply (derivedAbelianizationEquiv p hker).injective
    rw [MulEquiv.apply_symm_apply]
    exact congrArg Multiplicative.ofAdd hn⟩
  left_inv x := by
    apply Subtype.ext
    exact (derivedAbelianizationEquiv p hker).symm_apply_apply x.1
  right_inv w := by
    apply Subtype.ext
    exact congrArg Multiplicative.toAdd
      ((derivedAbelianizationEquiv p hker).apply_symm_apply
        (Multiplicative.ofAdd w.toAdd.1))
  map_mul' x y := by
    apply Subtype.ext
    exact congrArg Multiplicative.toAdd
      (map_mul (derivedAbelianizationEquiv p hker) x.1 y.1)

include hker in
theorem derivedNormalImage_card (N : Subgroup G) [N.Normal] :
    Nat.card (normalChainQuotient (commutator G) N) = Nat.card (primeDerivedImage p N) :=
  Nat.card_congr (derivedNormalImageEquiv p hker N).toEquiv

include hker in
theorem derivedNormalImage_log_card (N : Subgroup G) [N.Normal] :
    Nat.log p (Nat.card (normalChainQuotient (commutator G) N)) =
      Module.finrank (ZMod p) (primeDerivedImage p N) := by
  rw [derivedNormalImage_card p hker N,
    Module.natCard_eq_pow_finrank (K := ZMod p) (V := primeDerivedImage p N),
    Nat.card_zmod, Nat.log_pow (Fact.out : p.Prime).one_lt]

/-- Actual retained characters form a subspace of the joint annihilator
of W for the same original alternating-form family. -/
theorem retainedCharacters_le_derivedJointAnnihilator
    (N : Subgroup G) [N.Normal] (hDN : commutator G ≤ N) :
    normalChainRetainedCharacters (commutator G) N p hDN ≤
      linearJointAnnihilator (derivedEvaluationBilinearMap p hker) (primeDerivedImage p N) := by
  intro χ hχ v hv
  ext w
  exact retained_derivedEvaluationBilinear_eq_zero p hker N hDN χ hχ v hv w

/-- The promised generic head reduction. It retains the entire original
normal N, its actual image W and the same actual derived-character family. -/
theorem primeRelativeHead_above_derived_le_image_add_joint
    (N : Subgroup G) [N.Normal] (hDN : commutator G ≤ N) :
    Module.finrank (ZMod p) (primeRelativeCharacters p N) ≤
      Module.finrank (ZMod p) (primeDerivedImage p N) +
        Module.finrank (ZMod p)
          (linearJointAnnihilator (derivedEvaluationBilinearMap p hker) (primeDerivedImage p N)) := by
  have hq : Module.finrank (ZMod p)
      (primeRelativeCharacters p (normalChainQuotient (commutator G) N)) ≤
      Module.finrank (ZMod p) (primeDerivedImage p N) := by
    rw [← derivedNormalImage_log_card p hker N]
    exact (Submodule.finrank_le _).trans
      (Nat.le_log_of_pow_le (Fact.out : p.Prime).one_lt
        (primeCharacters_pow_finrank_le_card p (normalChainQuotient (commutator G) N)))
  rw [primeRelativeHead_chain_eq (commutator G) N p hDN]
  exact Nat.add_le_add hq
    (Submodule.finrank_mono (retainedCharacters_le_derivedJointAnnihilator p hker N hDN))

/-- A universal pair-kernel certificate controls every nonzero W at once. -/
theorem primeRelativeHead_above_derived_le_image_add_one
    (hpair : ∀ v : Fin 2 → primeRelativeCharacters p (commutator G),
      LinearIndependent (ZMod p) v →
        (derivedEvaluationBilinearMap p hker (v 0)).ker ⊓
          (derivedEvaluationBilinearMap p hker (v 1)).ker = ⊥)
    (N : Subgroup G) [N.Normal] (hDN : commutator G ≤ N)
    (hW : primeDerivedImage p N ≠ ⊥) :
    Module.finrank (ZMod p) (primeRelativeCharacters p N) ≤
      Module.finrank (ZMod p) (primeDerivedImage p N) + 1 :=
  (primeRelativeHead_above_derived_le_image_add_joint p hker N hDN).trans
    (Nat.add_le_add_left (linearJointAnnihilator_finrank_le_one
      (derivedEvaluationBilinearMap p hker) (primeDerivedImage p N) hpair hW) _)

/-- Large actual images have no retained contribution when every nonzero
actual commutator form has its stated radical bound. -/
theorem primeRelativeHead_above_derived_le_image_of_radical_bounds
    (a : ℕ)
    (hsingle : ∀ χ : primeRelativeCharacters p (commutator G), χ ≠ 0 →
      Module.finrank (ZMod p) (derivedEvaluationBilinearMap p hker χ).ker ≤ a)
    (N : Subgroup G) [N.Normal] (hDN : commutator G ≤ N)
    (hW : a < Module.finrank (ZMod p) (primeDerivedImage p N)) :
    Module.finrank (ZMod p) (primeRelativeCharacters p N) ≤
      Module.finrank (ZMod p) (primeDerivedImage p N) := by
  have h := primeRelativeHead_above_derived_le_image_add_joint p hker N hDN
  rw [linearJointAnnihilator_finrank_eq_zero_of_radical_bounds
    (derivedEvaluationBilinearMap p hker) (primeDerivedImage p N) a hsingle hW, Nat.add_zero] at h
  exact h

end SymmetricSubgroupAsymptotics
