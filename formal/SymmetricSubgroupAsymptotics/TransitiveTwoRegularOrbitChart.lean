import SymmetricSubgroupAsymptotics.BinaryPairParityAction

/-! A point chart for an original action with two regular normal orbits.

The translation group is the literal image on the first original orbit.
The second chart is transported by one actual outside element. Its
square is retained in the resulting point-action formula, so this does
not assume an involutory complement or a split top group.
-/
set_option autoImplicit false
noncomputable section
open scoped Classical Pointwise

namespace SymmetricSubgroupAsymptotics.TransitiveTwoRegularOrbitChart

open PermutationBinaryTwoOrbitSplit

variable {G X : Type} [Group G] [MulAction G X]
    (H : Subgroup G) [H.Normal]
    (o₁ o₂ : MulAction.orbitRel.Quotient H X)

/-- The literal image on the first original orbit. -/
abbrev TranslationGroup := (MulAction.toPermHom H o₁.orbit).range

variable (x₀ : o₁.orbit)
    (hregular : MulAction.stabilizer (TranslationGroup H o₁) x₀=⊥)

/-- Evaluation at an original point is the regular coordinate chart. -/
def regularEvalEquiv : TranslationGroup H o₁ ≃ o₁.orbit :=
  Equiv.ofBijective (fun v => v.val x₀) ⟨by
    intro s t he
    change s.val x₀ = t.val x₀ at he
    have hm : s⁻¹*t∈MulAction.stabilizer (TranslationGroup H o₁) x₀ := by
      apply MulAction.mem_stabilizer_iff.mpr
      change s.val⁻¹ (t.val x₀)=x₀
      rw [← he]
      exact Equiv.symm_apply_apply s.val x₀
    rw [hregular,Subgroup.mem_bot] at hm
    exact inv_mul_eq_one.mp hm,by
    intro y
    obtain ⟨h,hh⟩ := MulAction.exists_smul_eq H x₀ y
    exact ⟨(MulAction.toPermHom H o₁.orbit).rangeRestrict h,hh⟩⟩

@[simp] theorem regularEvalEquiv_apply (v : TranslationGroup H o₁) :
    regularEvalEquiv H o₁ x₀ hregular v=v.val x₀ := rfl

variable (g : G) (hg : g • o₁.orbit=o₂.orbit)
    (hne : o₁≠o₂)
    (hcover : ∀ o : MulAction.orbitRel.Quotient H X,o=o₁ ∨ o=o₂)

/-- Two copies of one actual regular image label the original point set.
The second copy is transported by the same actual outside element g. -/
def pointChart : TranslationGroup H o₁ ⊕ TranslationGroup H o₁ ≃ X :=
  Equiv.ofBijective (fun p => match p with
    | Sum.inl v => (regularEvalEquiv H o₁ x₀ hregular v).val
    | Sum.inr v => g • (regularEvalEquiv H o₁ x₀ hregular v).val) ⟨by
    intro p q he
    cases p with
    | inl v =>
      cases q with
      | inl w =>
        exact congrArg Sum.inl ((regularEvalEquiv H o₁ x₀ hregular).injective (Subtype.ext he))
      | inr w =>
        change (regularEvalEquiv H o₁ x₀ hregular v).val =
          g • (regularEvalEquiv H o₁ x₀ hregular w).val at he
        have hw : g • (regularEvalEquiv H o₁ x₀ hregular w).val∈o₂.orbit := by
          rw [← hg]
          exact Set.smul_mem_smul_set (regularEvalEquiv H o₁ x₀ hregular w).property
        have hv := (regularEvalEquiv H o₁ x₀ hregular v).property
        rw [he] at hv
        exact (hne ((MulAction.orbitRel.Quotient.mem_orbit.mp hv).symm.trans
          (MulAction.orbitRel.Quotient.mem_orbit.mp hw))).elim
    | inr v =>
      cases q with
      | inl w =>
        change g • (regularEvalEquiv H o₁ x₀ hregular v).val =
          (regularEvalEquiv H o₁ x₀ hregular w).val at he
        have hv : g • (regularEvalEquiv H o₁ x₀ hregular v).val∈o₂.orbit := by
          rw [← hg]
          exact Set.smul_mem_smul_set (regularEvalEquiv H o₁ x₀ hregular v).property
        rw [he] at hv
        have hw := (regularEvalEquiv H o₁ x₀ hregular w).property
        exact (hne ((MulAction.orbitRel.Quotient.mem_orbit.mp hw).symm.trans
          (MulAction.orbitRel.Quotient.mem_orbit.mp hv))).elim
      | inr w =>
        apply congrArg Sum.inr
        apply (regularEvalEquiv H o₁ x₀ hregular).injective
        apply Subtype.ext
        exact (MulAction.injective g) he,by
    intro x
    let o : MulAction.orbitRel.Quotient H X := Quotient.mk (MulAction.orbitRel H X) x
    have hx : x∈o.orbit := MulAction.orbitRel.Quotient.mem_orbit.mpr rfl
    rcases hcover o with ho | ho
    · have hx₁ : x∈o₁.orbit := ho ▸ hx
      exact ⟨Sum.inl ((regularEvalEquiv H o₁ x₀ hregular).symm ⟨x,hx₁⟩),
        congrArg Subtype.val ((regularEvalEquiv H o₁ x₀ hregular).apply_symm_apply _)⟩
    · have hx₂ : x∈o₂.orbit := ho ▸ hx
      let y := (orbitTranslation H o₁ o₂ g hg).symm ⟨x,hx₂⟩
      refine ⟨Sum.inr ((regularEvalEquiv H o₁ x₀ hregular).symm y),?_⟩
      change g • ((regularEvalEquiv H o₁ x₀ hregular)
        ((regularEvalEquiv H o₁ x₀ hregular).symm y)).val=x
      rw [Equiv.apply_symm_apply]
      exact congrArg Subtype.val ((orbitTranslation H o₁ o₂ g hg).apply_symm_apply ⟨x,hx₂⟩)⟩

@[simp] theorem pointChart_inl (v : TranslationGroup H o₁) :
    pointChart H o₁ o₂ x₀ hregular g hg hne hcover (Sum.inl v)=(v.val x₀).val := rfl

@[simp] theorem pointChart_inr (v : TranslationGroup H o₁) :
    pointChart H o₁ o₂ x₀ hregular g hg hne hcover (Sum.inr v)=g • (v.val x₀).val := rfl

/-- The two actual translation coordinates of the original H. -/
def translationPair : H →* TranslationGroup H o₁ × TranslationGroup H o₁ :=
  (MulAction.toPermHom H o₁.orbit).rangeRestrict.prod
    ((MulAction.toPermHom H o₁.orbit).rangeRestrict.comp (MulAut.conjNormal g⁻¹).toMonoidHom)

theorem normal_action_inl (h : H) (v : TranslationGroup H o₁) :
    (h:G) • pointChart H o₁ o₂ x₀ hregular g hg hne hcover (Sum.inl v)=
      pointChart H o₁ o₂ x₀ hregular g hg hne hcover
        (Sum.inl ((translationPair H o₁ g h).1*v)) := rfl

theorem normal_action_inr (h : H) (v : TranslationGroup H o₁) :
    (h:G) • pointChart H o₁ o₂ x₀ hregular g hg hne hcover (Sum.inr v)=
      pointChart H o₁ o₂ x₀ hregular g hg hne hcover
        (Sum.inr ((translationPair H o₁ g h).2*v)) := by
  change (h:G) • (g • (v.val x₀).val)=
    g • (((g⁻¹*(h:G)*(g⁻¹)⁻¹)) • (v.val x₀).val)
  simp only [inv_inv,mul_smul,smul_inv_smul]

theorem outside_action_inl (v : TranslationGroup H o₁) :
    g • pointChart H o₁ o₂ x₀ hregular g hg hne hcover (Sum.inl v)=
      pointChart H o₁ o₂ x₀ hregular g hg hne hcover (Sum.inr v) := rfl

/-- The original outside square remains as an actual translation. -/
theorem outside_action_inr (hgg : g*g∈H) (v : TranslationGroup H o₁) :
    g • pointChart H o₁ o₂ x₀ hregular g hg hne hcover (Sum.inr v)=
      pointChart H o₁ o₂ x₀ hregular g hg hne hcover
        (Sum.inl (((MulAction.toPermHom H o₁.orbit).rangeRestrict ⟨g*g,hgg⟩)*v)) := by
  change g • (g • (v.val x₀).val)=(g*g) • (v.val x₀).val
  exact (mul_smul g g _).symm

include x₀ hregular o₂ hg hne hcover in
/-- Both actual translation coordinates together recover the original
normal subgroup element, using the faithful original whole action. -/
theorem translationPair_injective [FaithfulSMul G X] :
    Function.Injective (translationPair H o₁ g) := by
  intro h h' he
  apply Subtype.ext
  apply FaithfulSMul.eq_of_smul_eq_smul (α := X)
  intro x
  obtain ⟨v,rfl⟩ := (pointChart H o₁ o₂ x₀ hregular g hg hne hcover).surjective x
  cases v with
  | inl v =>
    rw [normal_action_inl,normal_action_inl,congrArg Prod.fst he]
  | inr v =>
    rw [normal_action_inr,normal_action_inr,congrArg Prod.snd he]

theorem translationPair_fst_surjective :
    Function.Surjective (fun h : H => (translationPair H o₁ g h).1) :=
  (MulAction.toPermHom H o₁.orbit).rangeRestrict_surjective

theorem translationPair_snd_surjective :
    Function.Surjective (fun h : H => (translationPair H o₁ g h).2) :=
  (MulAction.toPermHom H o₁.orbit).rangeRestrict_surjective.comp
    (MulAut.conjNormal g⁻¹).surjective

end SymmetricSubgroupAsymptotics.TransitiveTwoRegularOrbitChart
