import SymmetricSubgroupAsymptotics.PrimeRelativeRadical
import Mathlib.LinearAlgebra.Dual.Lemmas

/-! Double-annihilator detection for the whole-original-group invariant
characters of an actual normal subgroup D. Characters vanishing on B≤D
detect B∨R_D, where R_D is the actual relative evaluation radical. The
radical is not silently discarded. A one-dimensional vanishing space
therefore identifies B∨R_D with a literal character kernel, and identifies
B itself only when R_D≤B has also been proved. -/
set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics

variable (p : ℕ) [Fact p.Prime]
    {G : Type*} [Group G] (D : Subgroup G) [D.Normal]

/-- Original whole-G invariant D-characters which vanish on B. No
normality of B is needed. The intended detection theorem supplies B≤D. -/
def primeRelativeCharactersVanishingOn (B : Subgroup G) :
    Submodule (ZMod p) (primeRelativeCharacters p D) where
  carrier := {χ | ∀ d : D, (d : G) ∈ B → χ.1 (Additive.ofMul d) = 0}
  zero_mem' := by intro d _; rfl
  add_mem' := by
    intro χ ψ hχ hψ d hd
    change χ.1 (Additive.ofMul d) + ψ.1 (Additive.ofMul d) = 0
    rw [hχ d hd, hψ d hd, add_zero]
  smul_mem' := by
    intro c χ hχ d hd
    change c • χ.1 (Additive.ofMul d) = 0
    rw [hχ d hd, smul_zero]

@[simp] theorem mem_primeRelativeCharactersVanishingOn_iff
    (B : Subgroup G) (χ : primeRelativeCharacters p D) :
    χ ∈ primeRelativeCharactersVanishingOn p D B ↔
      ∀ d : D, (d : G) ∈ B → χ.1 (Additive.ofMul d) = 0 := Iff.rfl

/-- Any individual vanishing character annihilates the entire original
join with the relative radical, not only the chosen generators of B. -/
theorem sup_primeRelativeRadical_le_mapped_character_ker
    (B : Subgroup G) (hBD : B ≤ D)
    (χ : primeRelativeCharacters p D)
    (hχ : χ ∈ primeRelativeCharactersVanishingOn p D B) :
    B ⊔ primeRelativeRadical p D ≤
      (AddMonoidHom.toMultiplicativeRight χ.1).ker.map D.subtype := by
  apply sup_le _ (primeRelativeRadical_le_mapped_character_ker p D χ)
  intro b hb
  exact ⟨⟨b, hBD hb⟩, hχ ⟨b, hBD hb⟩ hb, rfl⟩

variable [Finite G]

/-- Complete original invariant characters detect exactly B∨R_D.
The proof uses the actual image of B under relative evaluation and the
ordinary vector-space double annihilator, followed by reconstruction of
the same original element from B and the actual evaluation kernel. -/
theorem mem_sup_primeRelativeRadical_iff
    (B : Subgroup G) (hBD : B ≤ D) (d : D) :
    (d : G) ∈ B ⊔ primeRelativeRadical p D ↔
      ∀ χ : primeRelativeCharacters p D,
        χ ∈ primeRelativeCharactersVanishingOn p D B →
          χ.1 (Additive.ofMul d) = 0 := by
  classical
  constructor
  · intro hd χ hχ
    obtain ⟨e, he, hed⟩ :=
      sup_primeRelativeRadical_le_mapped_character_ker p D B hBD χ hχ hd
    have heq : e = d := Subtype.ext hed
    subst e
    exact he
  · intro hd
    let f : B →* Multiplicative (Module.Dual (ZMod p) (primeRelativeCharacters p D)) :=
      (primeRelativeEvaluation p D).comp (Subgroup.inclusion hBD)
    let fAdd : Additive B →+ Module.Dual (ZMod p) (primeRelativeCharacters p D) :=
      { toFun := fun b => (f b.toMul).toAdd
        map_zero' := congrArg Multiplicative.toAdd f.map_one
        map_add' := fun b c => congrArg Multiplicative.toAdd (f.map_mul b.toMul c.toMul) }
    let S : Submodule (ZMod p) (Module.Dual (ZMod p) (primeRelativeCharacters p D)) :=
      fAdd.range.toZModSubmodule p
    have hEval : (primeRelativeEvaluation p D d).toAdd ∈ S := by
      apply (Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff S _).mp
      intro ℓ hℓ
      obtain ⟨χ, rfl⟩ :=
        (Module.evalEquiv (ZMod p) (primeRelativeCharacters p D)).surjective ℓ
      change χ.1 (Additive.ofMul d) = 0
      apply hd χ
      intro e he
      have himage : (f (⟨(e : G), he⟩ : B)).toAdd ∈ S :=
        ⟨Additive.ofMul (⟨(e : G), he⟩ : B), rfl⟩
      have hz := (Submodule.mem_dualAnnihilator _).mp hℓ _ himage
      change χ.1 (Additive.ofMul e) = 0 at hz
      exact hz
    obtain ⟨b, hb⟩ := hEval
    let bD : D := ⟨(b.toMul : G), hBD b.toMul.2⟩
    have heval : primeRelativeEvaluation p D bD = primeRelativeEvaluation p D d := by
      apply Multiplicative.toAdd.injective
      exact hb
    have hdiff : bD⁻¹ * d ∈ primeRelativeRadicalKernel p D := by
      change primeRelativeEvaluation p D (bD⁻¹ * d) = 1
      rw [map_mul, map_inv, heval, inv_mul_cancel]
    have hB : (bD : G) ∈ B ⊔ primeRelativeRadical p D :=
      (show B ≤ B ⊔ primeRelativeRadical p D from le_sup_left) b.toMul.2
    have hR : ((bD⁻¹ * d : D) : G) ∈ B ⊔ primeRelativeRadical p D :=
      (show primeRelativeRadical p D ≤ B ⊔ primeRelativeRadical p D from le_sup_right)
        ⟨bD⁻¹ * d, hdiff, rfl⟩
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_cancel_left] using
      (B ⊔ primeRelativeRadical p D).mul_mem hB hR

/-- If the complete vanishing space is spanned by χ, its detection kernel
is the literal χ-kernel inside D, mapped through the original inclusion. -/
theorem sup_primeRelativeRadical_eq_mapped_character_ker_of_span
    (B : Subgroup G) (hBD : B ≤ D) (χ : primeRelativeCharacters p D)
    (hspan : primeRelativeCharactersVanishingOn p D B =
      Submodule.span (ZMod p) ({χ} : Set (primeRelativeCharacters p D))) :
    B ⊔ primeRelativeRadical p D =
      (AddMonoidHom.toMultiplicativeRight χ.1).ker.map D.subtype := by
  apply le_antisymm
  · apply sup_primeRelativeRadical_le_mapped_character_ker p D B hBD χ
    rw [hspan]
    exact Submodule.mem_span_singleton_self χ
  · rintro x ⟨d, hd, rfl⟩
    apply (mem_sup_primeRelativeRadical_iff p D B hBD d).mpr
    intro ψ hψ
    rw [hspan] at hψ
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hψ
    change c • χ.1 (Additive.ofMul d) = 0
    rw [show χ.1 (Additive.ofMul d) = 0 from hd, smul_zero]

/-- The same useful endpoint from an actual one-dimensional vanishing
space and any nonzero original member. No abstract character is substituted. -/
theorem sup_primeRelativeRadical_eq_mapped_character_ker_of_finrank_eq_one
    (B : Subgroup G) (hBD : B ≤ D) (χ : primeRelativeCharacters p D)
    (hχ : χ ∈ primeRelativeCharactersVanishingOn p D B) (hχ0 : χ ≠ 0)
    (hdim : Module.finrank (ZMod p) (primeRelativeCharactersVanishingOn p D B) = 1) :
    B ⊔ primeRelativeRadical p D =
      (AddMonoidHom.toMultiplicativeRight χ.1).ker.map D.subtype := by
  have hle : Submodule.span (ZMod p) ({χ} : Set (primeRelativeCharacters p D)) ≤
      primeRelativeCharactersVanishingOn p D B :=
    (Submodule.span_singleton_le_iff_mem χ _).mpr hχ
  have heq := Submodule.eq_of_le_of_finrank_eq hle
    ((finrank_span_singleton (K := ZMod p) hχ0).trans hdim.symm)
  exact sup_primeRelativeRadical_eq_mapped_character_ker_of_span p D B hBD χ heq.symm

/-- Only a separately proved containment R_D≤B permits removal of the
radical join and identification of B itself with the original χ-kernel. -/
theorem eq_mapped_character_ker_of_span_of_radical_le
    (B : Subgroup G) (hBD : B ≤ D) (hRB : primeRelativeRadical p D ≤ B)
    (χ : primeRelativeCharacters p D)
    (hspan : primeRelativeCharactersVanishingOn p D B =
      Submodule.span (ZMod p) ({χ} : Set (primeRelativeCharacters p D))) :
    B = (AddMonoidHom.toMultiplicativeRight χ.1).ker.map D.subtype := by
  have h := sup_primeRelativeRadical_eq_mapped_character_ker_of_span p D B hBD χ hspan
  rwa [sup_eq_left.mpr hRB] at h

theorem eq_mapped_character_ker_of_finrank_eq_one_of_radical_le
    (B : Subgroup G) (hBD : B ≤ D) (hRB : primeRelativeRadical p D ≤ B)
    (χ : primeRelativeCharacters p D)
    (hχ : χ ∈ primeRelativeCharactersVanishingOn p D B) (hχ0 : χ ≠ 0)
    (hdim : Module.finrank (ZMod p) (primeRelativeCharactersVanishingOn p D B) = 1) :
    B = (AddMonoidHom.toMultiplicativeRight χ.1).ker.map D.subtype := by
  have h := sup_primeRelativeRadical_eq_mapped_character_ker_of_finrank_eq_one
    p D B hBD χ hχ hχ0 hdim
  rwa [sup_eq_left.mpr hRB] at h

end SymmetricSubgroupAsymptotics
