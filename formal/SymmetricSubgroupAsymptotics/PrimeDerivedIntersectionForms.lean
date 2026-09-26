import SymmetricSubgroupAsymptotics.PrimeDerivedEvaluationPairing
import SymmetricSubgroupAsymptotics.FiniteQuotientDerivedIntersection
import SymmetricSubgroupAsymptotics.LinearJointAnnihilator

/-! Original derived characters vanishing on an actual subgroup B constrain
the original quotient-center directions. In particular, if N is normal in
the whole original group and N ∩ G′ ≤ B, these characters annihilate the
entire evaluation image of N. These are characters of G′ vanishing on B,
not characters of B asserted to extend to N. No splitting, intrinsic
derived-subgroup invariance, or enumeration of normal subgroups is used. -/
set_option autoImplicit false
noncomputable section
open scoped commutatorElement

namespace SymmetricSubgroupAsymptotics

variable (p : ℕ) [Fact p.Prime] {G : Type*} [Group G]

/-- Whole-G invariant characters of the original G′ which vanish on B.
For B≤G′ this is precisely the annihilator of B; the definition also makes
sense for arbitrary B by testing its actual intersection with G′. -/
def derivedCharactersVanishingOn (B : Subgroup G) :
    Submodule (ZMod p) (primeRelativeCharacters p (commutator G)) where
  carrier := {χ | ∀ d : commutator G, (d : G) ∈ B →
    χ.1 (Additive.ofMul d) = 0}
  zero_mem' := by intro d _; rfl
  add_mem' := by
    intro χ ψ hχ hψ d hd
    change χ.1 (Additive.ofMul d) + ψ.1 (Additive.ofMul d) = 0
    rw [hχ d hd, hψ d hd, add_zero]
  smul_mem' := by
    intro c χ hχ d hd
    change c • χ.1 (Additive.ofMul d) = 0
    rw [hχ d hd, smul_zero]

@[simp] theorem mem_derivedCharactersVanishingOn_iff
    (B : Subgroup G) (χ : primeRelativeCharacters p (commutator G)) :
    χ ∈ derivedCharactersVanishingOn p B ↔
      ∀ d : commutator G, (d : G) ∈ B → χ.1 (Additive.ofMul d) = 0 := Iff.rfl

/-- The actual relative radical is annihilated by every original derived
character, and the same holds for any original subgroup contained in it. -/
theorem derivedCharactersVanishingOn_eq_top_of_le_radical
    (B : Subgroup G) (hBR : B ≤ primeRelativeRadical p (commutator G)) :
    derivedCharactersVanishingOn p B = ⊤ := by
  apply top_unique
  intro χ _ d hd
  exact (mem_primeRelativeRadicalKernel_iff p (commutator G) d).mp
    ((coe_mem_primeRelativeRadical_iff p (commutator G) d).mp (hBR hd)) χ

@[simp] theorem derivedCharactersVanishingOn_radical :
    derivedCharactersVanishingOn p (primeRelativeRadical p (commutator G)) = ⊤ :=
  derivedCharactersVanishingOn_eq_top_of_le_radical p _ le_rfl

variable [Finite G]
variable (hker : (primeAbelianizationGroupMap p G).ker = commutator G)

/-- An original element central modulo B lies in every actual form radical
whose original derived character vanishes on B. Surjectivity of the original
evaluation map supplies every second argument of the form. -/
theorem derivedCharactersVanishingOn_eval_mem_ker
    (B : Subgroup G) [B.Normal]
    (χ : primeRelativeCharacters p (commutator G))
    (hχ : χ ∈ derivedCharactersVanishingOn p B)
    (x : G) (hx : x ∈ quotientCenterPreimage B) :
    primeAbelianizationMap p G (Additive.ofMul x) ∈
      (derivedEvaluationBilinearMap p hker χ).ker := by
  change derivedEvaluationBilinear p hker χ
    (primeAbelianizationMap p G (Additive.ofMul x)) = 0
  apply LinearMap.ext
  intro v
  obtain ⟨y, rfl⟩ := primeAbelianizationMap_surjective p G v
  change derivedEvaluationBilinear p hker χ
    (primeAbelianizationMap p G (Additive.ofMul x))
    (primeAbelianizationMap p G (Additive.ofMul y.toMul)) = 0
  rw [derivedEvaluationBilinear_eval]
  exact hχ (derivedCommutatorElement x y.toMul)
    ((mem_quotientCenterPreimage_iff_all_commutators B x).mp hx y.toMul)

/-- The entire original quotient-center image satisfies the joint
annihilator constraint, with no choice of lifts or basis. -/
theorem derivedCharactersVanishingOn_le_center_joint
    (B : Subgroup G) [B.Normal] :
    derivedCharactersVanishingOn p B ≤
      linearJointAnnihilator (derivedEvaluationBilinearMap p hker)
        (primeDerivedImage p (quotientCenterPreimage B)) := by
  intro χ hχ v hv
  obtain ⟨x, rfl⟩ :=
    (mem_primeDerivedImage_iff p (quotientCenterPreimage B) v).mp hv
  exact derivedCharactersVanishingOn_eval_mem_ker p hker B χ hχ x x.2

/-- Whole-G normality forces the original mixed commutators into the exact
intersection N ∩ G′. Thus even a certified upper subgroup B for that
intersection gives a necessary joint-annihilator condition on the same N. -/
theorem derivedCharactersVanishingOn_le_joint
    (B N : Subgroup G) [N.Normal] (hNB : N ⊓ commutator G ≤ B) :
    derivedCharactersVanishingOn p B ≤
      linearJointAnnihilator (derivedEvaluationBilinearMap p hker)
        (primeDerivedImage p N) := by
  intro χ hχ v hv
  obtain ⟨n, rfl⟩ := (mem_primeDerivedImage_iff p N v).mp hv
  change derivedEvaluationBilinear p hker χ
    (primeAbelianizationMap p G (Additive.ofMul (n : G))) = 0
  apply LinearMap.ext
  intro w
  obtain ⟨g, rfl⟩ := primeAbelianizationMap_surjective p G w
  change derivedEvaluationBilinear p hker χ
    (primeAbelianizationMap p G (Additive.ofMul (n : G)))
    (primeAbelianizationMap p G (Additive.ofMul g.toMul)) = 0
  rw [derivedEvaluationBilinear_eval]
  apply hχ (derivedCommutatorElement (n : G) g.toMul)
  apply hNB
  exact ⟨Subgroup.commutator_le_left N ⊤
      (Subgroup.commutator_mem_commutator n.2 (Subgroup.mem_top g.toMul)),
    (derivedCommutatorElement (n : G) g.toMul).2⟩

include hker in
/-- A zero image means containment in the actual original derived group
because this is the specified kernel of the original evaluation map. -/
theorem primeDerivedImage_eq_bot_iff_le_commutator (N : Subgroup G) :
    primeDerivedImage p N = ⊥ ↔ N ≤ commutator G := by
  constructor
  · intro hN x hx
    have hxker : x ∈ (primeAbelianizationGroupMap p G).ker := by
      change primeAbelianizationMap p G (Additive.ofMul x) = 0
      apply (Submodule.mem_bot (R := ZMod p)).mp
      rw [← hN]
      exact (mem_primeDerivedImage_iff p N _).mpr ⟨⟨x, hx⟩, rfl⟩
    rwa [hker] at hxker
  · intro hN
    apply le_antisymm _ bot_le
    intro v hv
    obtain ⟨n, rfl⟩ := (mem_primeDerivedImage_iff p N v).mp hv
    apply (Submodule.mem_bot (R := ZMod p)).mpr
    have hn : (n : G) ∈ (primeAbelianizationGroupMap p G).ker := by
      rw [hker]
      exact hN n.2
    exact hn

/-- Two dimensions of original characters vanishing on the intersection
force the entire original normal subgroup into G′ when every independent
pair of actual forms has zero common radical. -/
theorem derivedCharactersVanishingOn_image_eq_bot_of_two_le
    (hpair : ∀ v : Fin 2 → primeRelativeCharacters p (commutator G),
      LinearIndependent (ZMod p) v →
      (derivedEvaluationBilinearMap p hker (v 0)).ker ⊓
        (derivedEvaluationBilinearMap p hker (v 1)).ker = ⊥)
    (B N : Subgroup G) [N.Normal] (hNB : N ⊓ commutator G ≤ B)
    (htwo : 2 ≤ Module.finrank (ZMod p) (derivedCharactersVanishingOn p B)) :
    primeDerivedImage p N = ⊥ := by
  by_contra hW
  have hle := Submodule.finrank_mono
    (derivedCharactersVanishingOn_le_joint p hker B N hNB)
  have hone := linearJointAnnihilator_finrank_le_one
    (derivedEvaluationBilinearMap p hker) (primeDerivedImage p N) hpair hW
  exact (Nat.not_succ_le_self 1) (htwo.trans (hle.trans hone))

theorem derivedCharactersVanishingOn_normal_le_commutator_of_two_le
    (hpair : ∀ v : Fin 2 → primeRelativeCharacters p (commutator G),
      LinearIndependent (ZMod p) v →
      (derivedEvaluationBilinearMap p hker (v 0)).ker ⊓
        (derivedEvaluationBilinearMap p hker (v 1)).ker = ⊥)
    (B N : Subgroup G) [N.Normal] (hNB : N ⊓ commutator G ≤ B)
    (htwo : 2 ≤ Module.finrank (ZMod p) (derivedCharactersVanishingOn p B)) :
    N ≤ commutator G :=
  (primeDerivedImage_eq_bot_iff_le_commutator p hker N).mp
    (derivedCharactersVanishingOn_image_eq_bot_of_two_le p hker hpair B N hNB htwo)

/-- A nonzero vanishing-character parameter constrains the dimension of
the whole original image by the uniform single-form radical bound. -/
theorem derivedCharactersVanishingOn_image_finrank_le_of_one_le
    (a : ℕ)
    (hsingle : ∀ χ : primeRelativeCharacters p (commutator G), χ ≠ 0 →
      Module.finrank (ZMod p) (derivedEvaluationBilinearMap p hker χ).ker ≤ a)
    (B N : Subgroup G) [N.Normal] (hNB : N ⊓ commutator G ≤ B)
    (hone : 1 ≤ Module.finrank (ZMod p) (derivedCharactersVanishingOn p B)) :
    Module.finrank (ZMod p) (primeDerivedImage p N) ≤ a := by
  by_contra hW
  have hzero := linearJointAnnihilator_finrank_eq_zero_of_radical_bounds
    (derivedEvaluationBilinearMap p hker) (primeDerivedImage p N) a hsingle
    (lt_of_not_ge hW)
  have hle := Submodule.finrank_mono
    (derivedCharactersVanishingOn_le_joint p hker B N hNB)
  rw [hzero] at hle
  exact (Nat.not_succ_le_zero 0) (hone.trans hle)

end SymmetricSubgroupAsymptotics
