import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoFourPairsClassification
import SymmetricSubgroupAsymptotics.CyclicSocleQuotientTools

/-! Construct the four-pair character branch from a unique normal kernel.
Only a literal small permutation quotient and a normal-cover property are
needed. The all-original-normal-quotient one-slot interval is proved here;
it is not supplied as a catalogue field. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace FourPairNormalCover

/-- A unique nontrivial normal kernel gives the exact one-slot character
interval. Normals outside the retained kernel filter are proved to be the
original bottom subgroup; no selected normal census is used. -/
def characterModel {U : PreE7NonPairActionClass 8} {d : ℕ}
    (q : preE7NonPairAction 8 U →* Equiv.Perm (Fin d))
    (hd : d ≤ 6) (hne : q.ker ≠ ⊥)
    (hcover : ∀ N : Subgroup (preE7NonPairAction 8 U),
      N.Normal → N ≠ ⊥ → q.ker ≤ N) : CertifiedFourPairCharacterModel U where
  interval := {
    E := q.ker
    quotientDegree := d
    quotientAction := q.range.subtype.comp
      (QuotientGroup.quotientKerEquivRange q).toMonoidHom
    quotientAction_injective := Subtype.val_injective.comp
      (QuotientGroup.quotientKerEquivRange q).injective
    slots := 1
    quotientSocleGenerators := by
      intro N hN
      letI : N.1.Normal := N.2
      have hbot : N.1 = ⊥ := by
        by_contra hn
        exact hN (hcover N.1 N.2 hn)
      let e : (preE7NonPairAction 8 U ⧸ N.1) ≃*
          preE7NonPairAction 8 U :=
        (QuotientGroup.quotientMulEquivOfEq hbot).trans
          QuotientGroup.quotientBot
      exact CyclicSocleQuotientTools.socleBound_equiv e.symm
        (CyclicSocleQuotientTools.socleBound_of_normal_cover q.ker hne hcover) }
  quotientDegree_le_six := hd
  slots_eq_one := rfl

/-- Install the proved interval into the existing exhaustive row interface. -/
def row {U : PreE7NonPairActionClass 8} {d : ℕ}
    (q : preE7NonPairAction 8 U →* Equiv.Perm (Fin d))
    (hd : d ≤ 6) (hne : q.ker ≠ ⊥)
    (hcover : ∀ N : Subgroup (preE7NonPairAction 8 U),
      N.Normal → N ≠ ⊥ → q.ker ≤ N) : PublishedDegreeTwoFourPairRow U :=
  .character (characterModel q hd hne hcover)


/-- Transfer a named model's normal-cover theorem to the literal original
source before constructing its retained interval. The denominator N is
mapped and pulled back through the same exact group equivalence. -/
def characterModel_of_equiv {U : PreE7NonPairActionClass 8}
    {G : Type} [Group G] {d : ℕ}
    (e : preE7NonPairAction 8 U ≃* G)
    (q : G →* Equiv.Perm (Fin d)) (hd : d ≤ 6)
    (hne : q.ker ≠ ⊥)
    (hcover : ∀ N : Subgroup G, N.Normal → N ≠ ⊥ → q.ker ≤ N) :
    CertifiedFourPairCharacterModel U := by
  let f := q.comp e.toMonoidHom
  have hfne : f.ker ≠ ⊥ := by
    intro hf
    apply hne
    apply le_antisymm ?_ bot_le
    intro g hg
    have hx : e.symm g ∈ f.ker := by
      change q (e (e.symm g)) = 1
      simpa only [e.apply_symm_apply] using hg
    rw [hf] at hx
    have hx1 := Subgroup.mem_bot.mp hx
    have he := congrArg e hx1
    simpa only [e.apply_symm_apply, e.map_one] using he
  apply characterModel f hd hfne
  intro N hN hNb x hx
  let M := N.map e.toMonoidHom
  have hM : M.Normal := hN.map e.toMonoidHom e.surjective
  have hMb : M ≠ ⊥ := by
    intro hb
    apply hNb
    apply le_antisymm ?_ bot_le
    intro n hn
    have hm : e n ∈ M := ⟨n, hn, rfl⟩
    rw [hb] at hm
    have he := Subgroup.mem_bot.mp hm
    exact Subgroup.mem_bot.mpr (e.injective (he.trans e.map_one.symm))
  have hx' : e x ∈ q.ker := hx
  obtain ⟨n, hn, he⟩ := hcover M hM hMb hx'
  have hnx : n = x := e.injective he
  exact hnx ▸ hn


/-- The existing GL2(3) projective normal-cover proof constructs a
four-pair character certificate from only the exact group recognition. -/
def glModel {U : PreE7NonPairActionClass 8}
    (e : preE7NonPairAction 8 U ≃* LinearThree.GL3) :
    CertifiedFourPairCharacterModel U := by
  apply characterModel_of_equiv e LinearThree.projective (by norm_num)
  · intro hbot
    have h := LinearThree.card_ker_projective
    rw [hbot] at h
    norm_num at h
  · exact LinearThree.normal_cover


/-- The SL2(3) projective quotient is retained in its faithful four-point
A4 action; its known two-element kernel supplies the unique normal axis. -/
def slModel {U : PreE7NonPairActionClass 8}
    (e : preE7NonPairAction 8 U ≃* LinearThree.SL3) :
    CertifiedFourPairCharacterModel U := by
  let q := NaturalS4.a4.subtype.comp LinearThree.projectiveSL
  have hker : q.ker = LinearThree.projectiveSL.ker := by
    ext x
    change ((LinearThree.projectiveSL x : NaturalS4.a4) :
      Equiv.Perm (Fin 4)) = 1 ↔ LinearThree.projectiveSL x = 1
    exact ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩
  apply characterModel_of_equiv e q (by norm_num)
  · rw [hker]
    intro hbot
    have h := LinearThree.card_ker_projectiveSL
    rw [hbot] at h
    norm_num at h
  · intro N hN hNb
    rw [hker]
    exact LinearThree.normal_cover_SL N hN hNb

end FourPairNormalCover
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics
