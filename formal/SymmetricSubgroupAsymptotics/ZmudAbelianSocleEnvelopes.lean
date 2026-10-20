import SymmetricSubgroupAsymptotics.ZmudAbelianSocleCharacters

/-! Coinducing the whole-socle characters yields the abelian part of the
faithful tuple construction. The same envelopes are trivial on every
nonabelian minimal normal subgroup, so they can be tensored with the
nonabelian detector without changing either type's fixed spaces. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.ZmudAbelianSocleEnvelopes

open ZmudFixedSpaceConstituents ZmudCoinducedEnvelopes

/-- Trivial action of an ambient-normal subgroup also survives literal
coinduction. -/
theorem coinduced_trivial
    {k G V : Type} [Field k] [Group G] [AddCommGroup V] [Module k V]
    (H N : Subgroup G) [N.Normal] (hNH : N ≤ H)
    (sigma : Representation k H V)
    (htriv : ∀ (n : N) (v : V), sigma ⟨n.1, hNH n.2⟩ v = v)
    (n : N) (f : Representation.coindV H.subtype sigma) :
    Representation.coind H.subtype sigma n.1 f = f := by
  apply Subtype.ext
  funext g
  let m : N := ⟨g * n.1 * g⁻¹,
    Subgroup.Normal.conj_mem inferInstance n.1 n.2 g⟩
  have hmul : m.1 * g = g * n.1 := by dsimp only [m]; group
  change f.1 (g * n.1) = f.1 g
  rw [← hmul]
  change f.1 (H.subtype (⟨m.1, hNH m.2⟩ : H) * g) = f.1 g
  rw [f.2 (⟨m.1, hNH m.2⟩ : H) g]
  exact htriv m (f.1 g)

/-- The complete abelian-socle envelope tuple, retaining trivial action
on all nonabelian ambient minimal normals. -/
theorem exists_envelopes
    {G : Type} [Group G] [Finite G] {t : ℕ}
    (ht : SocleNormalGeneratorBound G t) :
    ∃ E : Fin t → Envelope G,
      (∀ (N : Subgroup G) (hN : IsMinimalNormalSubgroup N), IsMulCommutative N →
        ∃ i : Fin t, ∀ v : (E i).Space,
          (∀ n : N, (E i).action n.1 v = v) → v = 0) ∧
      ∀ (N : Subgroup G) (hN : IsMinimalNormalSubgroup N), ¬ IsMulCommutative N →
        ∀ (i : Fin t) (n : N) (v : (E i).Space), (E i).action n.1 v = v := by
  obtain ⟨chi, hdetect, htriv⟩ := ZmudAbelianSocleCharacters.exists_characters ht
  let E : Fin t → Envelope G := fun i => scalarEnvelope (finiteGroupSocle G) (chi i)
  refine ⟨E, ?_, ?_⟩
  · intro N hN hcomm
    letI : N.Normal := hN.1
    have hNS : N ≤ finiteGroupSocle G := fun n hn =>
      Subgroup.subset_normalClosure ⟨N, hN, hn⟩
    obtain ⟨i, n, hn⟩ := hdetect N hN hcomm
    refine ⟨i, ?_⟩
    intro v hv
    exact scalarEnvelope_fixedFree (finiteGroupSocle G) N hNS (chi i) ⟨n, hn⟩ v hv
  · intro N hN hnoncomm i n v
    letI : N.Normal := hN.1
    have hNS : N ≤ finiteGroupSocle G := fun n hn =>
      Subgroup.subset_normalClosure ⟨N, hN, hn⟩
    apply coinduced_trivial (finiteGroupSocle G) N hNS
      (scalarCharacterRepresentation (chi i)) ?_ n v
    intro m z
    change chi i ⟨m.1, hNS m.2⟩ * z = z
    rw [htriv N hN hnoncomm i m, one_mul]

end SymmetricSubgroupAsymptotics.ZmudAbelianSocleEnvelopes
