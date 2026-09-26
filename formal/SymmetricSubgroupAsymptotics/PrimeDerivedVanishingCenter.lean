import SymmetricSubgroupAsymptotics.PrimeRelativeCharacterDetection
import SymmetricSubgroupAsymptotics.PrimeDerivedIntersectionForms
import SymmetricSubgroupAsymptotics.PrimeDerivedIntersectionImage

/-! Complete vanishing-character detection of the original quotient
center. The entire actual parameter subspace is retained; it need not be
one-dimensional. Containment of the actual relative radical in B is an
explicit hypothesis of the reverse detection and exact cardinal formula. -/
set_option autoImplicit false
noncomputable section
open scoped commutatorElement

namespace SymmetricSubgroupAsymptotics

variable (p : ℕ) [Fact p.Prime] {G : Type*} [Group G] [Finite G]

/-- Every subgroup between an original normal subgroup's invariant
evaluation radical and that subgroup is normal in the whole original G.
This follows from actual invariant-character detection, not from a
subgroup-normality claim inside an abelian replacement group. -/
theorem subgroup_normal_of_primeRelativeRadical_le
    (D : Subgroup G) [D.Normal] (B : Subgroup G)
    (hBD : B ≤ D) (hRB : primeRelativeRadical p D ≤ B) : B.Normal := ⟨by
  intro x hx g
  have hd : g * x * g⁻¹ ∈ D :=
    Subgroup.Normal.conj_mem inferInstance x (hBD hx) g
  have hj : g * x * g⁻¹ ∈ B ⊔ primeRelativeRadical p D := by
    apply (mem_sup_primeRelativeRadical_iff p D B hBD ⟨g * x * g⁻¹, hd⟩).mpr
    intro χ hχ
    exact (χ.2 g ⟨x, hBD hx⟩).trans (hχ ⟨x, hBD hx⟩ hx)
  simpa only [sup_eq_left.mpr hRB] using hj⟩

variable (hker : (primeAbelianizationGroupMap p G).ker = commutator G)

/-- The common radical is indexed by every actual whole-G invariant
derived character vanishing on B, including the zero character. -/
def derivedVanishingCommonRadical (B : Subgroup G) :
    Submodule (ZMod p) (PrimeAbelianization p G) :=
  ⨅ χ : derivedCharactersVanishingOn p B,
    (derivedEvaluationBilinearMap p hker (χ : primeRelativeCharacters p (commutator G))).ker

@[simp] theorem mem_derivedVanishingCommonRadical_iff
    (B : Subgroup G) (v : PrimeAbelianization p G) :
    v ∈ derivedVanishingCommonRadical p hker B ↔
      ∀ χ ∈ derivedCharactersVanishingOn p B,
        derivedEvaluationBilinearMap p hker χ v = 0 := by
  simp only [derivedVanishingCommonRadical, Submodule.mem_iInf, LinearMap.mem_ker,
    Subtype.forall]

/-- The same original element is central modulo B exactly when its
evaluation lies in the complete vanishing-family common radical.
The reverse direction detects B itself only because R_D≤B is explicit. -/
theorem mem_quotientCenterPreimage_iff_derivedVanishingCommonRadical
    (B : Subgroup G) [B.Normal] (hBD : B ≤ commutator G)
    (hRB : primeRelativeRadical p (commutator G) ≤ B) (x : G) :
    x ∈ quotientCenterPreimage B ↔
      primeAbelianizationMap p G (Additive.ofMul x) ∈
        derivedVanishingCommonRadical p hker B := by
  constructor
  · intro hx
    apply (mem_derivedVanishingCommonRadical_iff p hker B _).mpr
    intro χ hχ
    exact derivedCharactersVanishingOn_eval_mem_ker p hker B χ hχ x hx
  · intro hx
    apply (mem_quotientCenterPreimage_iff_all_commutators B x).mpr
    intro y
    have hj : (derivedCommutatorElement x y : G) ∈
        B ⊔ primeRelativeRadical p (commutator G) := by
      apply (mem_sup_primeRelativeRadical_iff p (commutator G) B hBD
        (derivedCommutatorElement x y)).mpr
      intro χ hχ
      change χ ∈ derivedCharactersVanishingOn p B at hχ
      have hzero : derivedEvaluationBilinear p hker χ
          (primeAbelianizationMap p G (Additive.ofMul x)) = 0 :=
        (mem_derivedVanishingCommonRadical_iff p hker B _).mp hx χ hχ
      have heval := LinearMap.congr_fun hzero
        (primeAbelianizationMap p G (Additive.ofMul y))
      rw [derivedEvaluationBilinear_eval] at heval
      exact heval
    simpa only [sup_eq_left.mpr hRB] using hj

include hker in
/-- The original derived group really is contained in this original
center preimage before any quotient or cardinal simplification is taken. -/
theorem commutator_le_quotientCenterPreimage_of_relativeRadical_le
    (B : Subgroup G) [B.Normal] (hBD : B ≤ commutator G)
    (hRB : primeRelativeRadical p (commutator G) ≤ B) :
    commutator G ≤ quotientCenterPreimage B := by
  intro x hx
  apply (mem_quotientCenterPreimage_iff_derivedVanishingCommonRadical
    p hker B hBD hRB x).mpr
  have hz : primeAbelianizationMap p G (Additive.ofMul x) = 0 := by
    have hm : x ∈ (primeAbelianizationGroupMap p G).ker := by rwa [hker]
    exact hm
  rw [hz]
  exact Submodule.zero_mem _

/-- Every common-radical direction is represented by an element of the
same original center preimage, using the surjective original evaluation. -/
theorem primeDerivedImage_quotientCenterPreimage_vanishing
    (B : Subgroup G) [B.Normal] (hBD : B ≤ commutator G)
    (hRB : primeRelativeRadical p (commutator G) ≤ B) :
    primeDerivedImage p (quotientCenterPreimage B) =
      derivedVanishingCommonRadical p hker B := by
  apply le_antisymm
  · intro v hv
    obtain ⟨x, rfl⟩ := (mem_primeDerivedImage_iff p _ v).mp hv
    exact (mem_quotientCenterPreimage_iff_derivedVanishingCommonRadical
      p hker B hBD hRB x).mp x.2
  · intro v hv
    obtain ⟨x, rfl⟩ := primeAbelianizationMap_surjective p G v
    apply (mem_primeDerivedImage_iff p _ _).mpr
    exact ⟨⟨x.toMul,
      (mem_quotientCenterPreimage_iff_derivedVanishingCommonRadical
        p hker B hBD hRB x.toMul).mpr hv⟩, rfl⟩

/-- This is an equivalence of the actual quotient image with the complete
common radical; no selected parameter list replaces the character space. -/
def derivedVanishingCenterEquiv
    (B : Subgroup G) [B.Normal] (hBD : B ≤ commutator G)
    (hRB : primeRelativeRadical p (commutator G) ≤ B) :
    normalChainQuotient (commutator G) (quotientCenterPreimage B) ≃*
      Multiplicative (derivedVanishingCommonRadical p hker B) :=
  (derivedNormalImageEquiv p hker (quotientCenterPreimage B)).trans
    (LinearEquiv.ofEq _ _
      (primeDerivedImage_quotientCenterPreimage_vanishing p hker B hBD hRB)).toAddEquiv.toMultiplicative

/-- Exact original center-preimage order for every parameter dimension,
with the actual derived-group order and radical containment retained. -/
theorem quotientCenterPreimage_vanishing_card
    (B : Subgroup G) [B.Normal] (hBD : B ≤ commutator G)
    (hRB : primeRelativeRadical p (commutator G) ≤ B) :
    Nat.card (quotientCenterPreimage B) =
      p ^ Module.finrank (ZMod p) (derivedVanishingCommonRadical p hker B) *
        Nat.card (commutator G) := by
  have h := primeDerivedImage_pow_finrank_mul_intersection p hker
    (quotientCenterPreimage B)
  rw [primeDerivedImage_quotientCenterPreimage_vanishing p hker B hBD hRB,
    inf_eq_right.mpr
      (commutator_le_quotientCenterPreimage_of_relativeRadical_le p hker B hBD hRB)] at h
  exact h.symm

end SymmetricSubgroupAsymptotics
