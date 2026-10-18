import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoFourPairsNormalCover

/-! Retained original-normal intervals through a monolithic kernel.
The first kernel need not itself be the final comparator kernel. This is
what allows the Y2--Y5 central quotient to be compressed a second time. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace FourPairRetainedChain

/-- Descend each nonbottom original denominator through the same actual
onto map. This is reusable with a proved lower retained interval. -/
theorem retained_socle {G H : Type} [Group G] [Group H]
    (q : G →* H) (hq : Function.Surjective q)
    (hne : q.ker ≠ ⊥)
    (hcover : ∀ N : Subgroup G, N.Normal → N ≠ ⊥ → q.ker ≤ N)
    (D : Subgroup H)
    (lower : ∀ (M : Subgroup H) [M.Normal], ¬ D ≤ M →
      SocleNormalGeneratorBound (H ⧸ M) 1)
    (N : Subgroup G) [N.Normal] (hN : ¬ D.comap q ≤ N) :
    SocleNormalGeneratorBound (G ⧸ N) 1 := by
  by_cases hbot : N = ⊥
  · let e : (G ⧸ N) ≃* G :=
      (QuotientGroup.quotientMulEquivOfEq hbot).trans QuotientGroup.quotientBot
    exact CyclicSocleQuotientTools.socleBound_equiv e.symm
      (CyclicSocleQuotientTools.socleBound_of_normal_cover q.ker hne hcover)
  · have hker : q.ker ≤ N := hcover N inferInstance hbot
    let M := N.map q
    have hM : M.Normal := (inferInstance : N.Normal).map q hq
    have hnot : ¬ D ≤ M := by
      intro hDM
      apply hN
      calc
        D.comap q ≤ M.comap q := Subgroup.comap_mono hDM
        _ = N := Subgroup.comap_map_eq_self hker
    letI : M.Normal := hM
    let e : (G ⧸ N) ≃* (H ⧸ M) := quotientEquivOfKerLe q hq N hker
    exact CyclicSocleQuotientTools.socleBound_equiv e.symm (lower M hnot)

/-- A second unique-normal-kernel quotient supplies its lower retained
interval structurally: its only retained denominator is bottom. -/
theorem lower_of_normalCover {H K : Type} [Group H] [Group K]
    (r : H →* K) (hne : r.ker ≠ ⊥)
    (hcover : ∀ M : Subgroup H, M.Normal → M ≠ ⊥ → r.ker ≤ M)
    (M : Subgroup H) [M.Normal] (hnot : ¬ r.ker ≤ M) :
    SocleNormalGeneratorBound (H ⧸ M) 1 := by
  have hbot : M = ⊥ := by
    by_contra hn
    exact hnot (hcover M inferInstance hn)
  let e : (H ⧸ M) ≃* H :=
    (QuotientGroup.quotientMulEquivOfEq hbot).trans QuotientGroup.quotientBot
  exact CyclicSocleQuotientTools.socleBound_equiv e.symm
    (CyclicSocleQuotientTools.socleBound_of_normal_cover r.ker hne hcover)

/-- The two-stage monolithic chain constructs the original one-slot
interval with the final small comparator, not the possibly large central
quotient. No all-original-quotients source bound is supplied. -/
def characterModel {U : PreE7NonPairActionClass 8}
    {H : Type} [Group H] {d : ℕ}
    (q : preE7NonPairAction 8 U →* H) (hq : Function.Surjective q)
    (hqne : q.ker ≠ ⊥)
    (hqcover : ∀ N : Subgroup (preE7NonPairAction 8 U),
      N.Normal → N ≠ ⊥ → q.ker ≤ N)
    (r : H →* Equiv.Perm (Fin d)) (hd : d ≤ 6)
    (hrne : r.ker ≠ ⊥)
    (hrcover : ∀ M : Subgroup H, M.Normal → M ≠ ⊥ → r.ker ≤ M) :
    CertifiedFourPairCharacterModel U where
  interval := {
    E := (r.comp q).ker
    quotientDegree := d
    quotientAction := (r.comp q).range.subtype.comp
      (QuotientGroup.quotientKerEquivRange (r.comp q)).toMonoidHom
    quotientAction_injective := Subtype.val_injective.comp
      (QuotientGroup.quotientKerEquivRange (r.comp q)).injective
    slots := 1
    quotientSocleGenerators := by
      intro N hN
      letI : N.1.Normal := N.2
      apply retained_socle q hq hqne hqcover r.ker
        (lower_of_normalCover r hrne hrcover) N.1
      exact hN }
  quotientDegree_le_six := hd
  slots_eq_one := rfl


/-- A named quotient recognized by an actual onto map and a proved unique
minimal normal core. This is structural data, not a source bound. -/
structure MonolithicQuotient (H : Type) [Group H] where
  Target : Type
  [targetGroup : Group Target]
  pi : H →* Target
  onto : Function.Surjective pi
  core : Subgroup Target
  [coreNormal : core.Normal]
  core_ne_bot : core ≠ ⊥
  cover : ∀ K : Subgroup Target, K.Normal → K ≠ ⊥ → core ≤ K

attribute [instance] MonolithicQuotient.targetGroup MonolithicQuotient.coreNormal

/-- A finite structural normal menu and one exact cyclic socle witness
construct the lower retained interval. This includes the three-line Xg
case: the bottom socle uses one cyclic vector and each line quotient is
recognized as a monolithic S4 model. -/
theorem lower_of_finiteMenu {H : Type} [Group H] (D : Subgroup H)
    {n : ℕ} (models : Fin n → MonolithicQuotient H)
    (v : H)
    (hcyclic : Subgroup.normalClosure (Set.range (fun _ : Fin 1 => v)) =
      finiteGroupSocle H)
    (menu : ∀ M : Subgroup H, M.Normal → ¬ D ≤ M →
      M = ⊥ ∨ ∃ i, M = (models i).pi.ker)
    (M : Subgroup H) [M.Normal] (hM : ¬ D ≤ M) :
    SocleNormalGeneratorBound (H ⧸ M) 1 := by
  rcases menu M inferInstance hM with hb | hm
  · let e : (H ⧸ M) ≃* H :=
      (QuotientGroup.quotientMulEquivOfEq hb).trans QuotientGroup.quotientBot
    exact CyclicSocleQuotientTools.socleBound_equiv e.symm ⟨fun _ => v, hcyclic⟩
  · obtain ⟨i, hi⟩ := hm
    let e : (H ⧸ M) ≃* (models i).Target :=
      (QuotientGroup.quotientMulEquivOfEq hi).trans
        (QuotientGroup.quotientKerEquivOfSurjective (models i).pi (models i).onto)
    exact CyclicSocleQuotientTools.socleBound_equiv e.symm
      (CyclicSocleQuotientTools.socleBound_of_normal_cover
        (models i).core (models i).core_ne_bot (models i).cover)

/-- Original character interval from a monolithic outer kernel and a
finite lower normal menu. All original denominators are discharged by
retained_socle and the explicit lower witness/menu. -/
def characterModel_of_finiteMenu {U : PreE7NonPairActionClass 8}
    {H : Type} [Group H] {d n : ℕ}
    (q : preE7NonPairAction 8 U →* H) (hq : Function.Surjective q)
    (hqne : q.ker ≠ ⊥)
    (hqcover : ∀ N : Subgroup (preE7NonPairAction 8 U),
      N.Normal → N ≠ ⊥ → q.ker ≤ N)
    (r : H →* Equiv.Perm (Fin d)) (hd : d ≤ 6)
    (models : Fin n → MonolithicQuotient H) (v : H)
    (hcyclic : Subgroup.normalClosure (Set.range (fun _ : Fin 1 => v)) =
      finiteGroupSocle H)
    (menu : ∀ M : Subgroup H, M.Normal → ¬ r.ker ≤ M →
      M = ⊥ ∨ ∃ i, M = (models i).pi.ker) :
    CertifiedFourPairCharacterModel U where
  interval := {
    E := (r.comp q).ker
    quotientDegree := d
    quotientAction := (r.comp q).range.subtype.comp
      (QuotientGroup.quotientKerEquivRange (r.comp q)).toMonoidHom
    quotientAction_injective := Subtype.val_injective.comp
      (QuotientGroup.quotientKerEquivRange (r.comp q)).injective
    slots := 1
    quotientSocleGenerators := by
      intro N hN
      letI : N.1.Normal := N.2
      apply retained_socle q hq hqne hqcover r.ker
        (lower_of_finiteMenu r.ker models v hcyclic menu) N.1
      exact hN }
  quotientDegree_le_six := hd
  slots_eq_one := rfl

end FourPairRetainedChain
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics
