import SymmetricSubgroupAsymptotics.ZmudPrimeSocleDualDetectors
import SymmetricSubgroupAsymptotics.ZmudCoinducedEnvelopes
import SymmetricSubgroupAsymptotics.ZmudSoclePrimaryProjections

/-! Primary socle dual vectors give complex characters of the entire
literal socle. They jointly detect every minimal normal subgroup of that
prime and are trivial on every minimal normal subgroup of a different
type. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.ZmudPrimarySocleCharacters

open ZmudCoinducedEnvelopes

variable {G : Type} [Group G] [Finite G]

private theorem factor_nonzero
    (E : Subgroup G) [E.Normal] (C : ElementaryMinimalNormalChart E)
    (N : Subgroup G) [N.Normal] (hNE : N ≤ E) (hN : N ≠ ⊥) :
    C.originalKernelChart.normalSubrepresentation
      (QuotientGroup.mk' E) (QuotientGroup.mk'_surjective E)
      C.quotientRepresentation N ≠ ⊥ := by
  intro hbot
  obtain ⟨n, hn⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hN
  let e : E := ⟨n.1, hNE n.2⟩
  have hm := (elementaryIntersectionModule_mem_iff E C N e).mpr n.2
  change (C.equiv e).toAdd ∈ C.originalKernelChart.normalSubrepresentation
    (QuotientGroup.mk' E) (QuotientGroup.mk'_surjective E)
    C.quotientRepresentation N at hm
  rw [hbot] at hm
  have hz : (C.equiv e).toAdd = 0 := hm
  have he : e = 1 := by
    apply C.equiv.injective
    apply Multiplicative.toAdd.injective
    simpa only [map_one] using hz
  exact hn (Subtype.ext (congrArg (fun z : E => (z : G)) he))

/-- A primary detector tuple, extended to the literal whole socle. -/
theorem exists_characters
    (p : ℕ) [Fact p.Prime] (P : Subgroup G → Prop)
    {t : ℕ} (ht : SocleNormalGeneratorBound G t) :
    ∃ chi : Fin t → (finiteGroupSocle G →* ℂ),
      (∀ (N : Subgroup G) (hN : IsMinimalNormalSubgroup N), P N → IsPGroup p N →
        ∃ (i : Fin t) (n : N),
          chi i ⟨n.1, Subgroup.subset_normalClosure ⟨N, hN, n.2⟩⟩ ≠ 1) ∧
      ∀ (N : Subgroup G) (hN : IsMinimalNormalSubgroup N), ¬ IsPGroup p N →
        ∀ (i : Fin t) (n : N),
          chi i ⟨n.1, Subgroup.subset_normalClosure ⟨N, hN, n.2⟩⟩ = 1 := by
  let E := minimalNormalSoclePart G (fun M => P M ∧ IsPGroup p M)
  let C := selectedPrimeSoclePartElementaryChart (G := G) p P
  have hEsocle : E ≤ finiteGroupSocle G :=
    minimalNormalSoclePart_le_finiteGroupSocle G _
  have hEp : IsPGroup p E := primePrimarySoclePart_isPGroup_of_predicate p G P
  obtain ⟨l, hl⟩ := ZmudPrimeSocleDualDetectors.primeSocle_exists_dual_detectors p G P ht
  let theta : Fin t → E →* ℂ := fun i =>
    (elementaryCharacter (l i)).comp C.equiv.toMonoidHom
  choose chi hleft hother using fun i =>
    ZmudSoclePrimaryProjections.exists_primary_character_extension
      p E hEp hEsocle (theta i)
  refine ⟨chi, ?_, ?_⟩
  · intro N hN hPN hpN
    letI : N.Normal := hN.1
    have hNE : N ≤ E :=
      minimalNormal_le_minimalNormalSoclePart _ N hN ⟨hPN, hpN⟩
    let S := C.originalKernelChart.normalSubrepresentation
      (QuotientGroup.mk' E) (QuotientGroup.mk'_surjective E)
      C.quotientRepresentation N
    obtain ⟨i, v, hv, hlnz⟩ := hl S (factor_nonzero E C N hNE hN.2.1)
    let e : E := C.equiv.symm (Multiplicative.ofAdd v)
    have hecoord : (C.equiv e).toAdd = v := by
      dsimp only [e]
      rw [MulEquiv.apply_symm_apply]
      rfl
    have heN : e.1 ∈ N :=
      (elementaryIntersectionModule_mem_iff E C N e).mp (hecoord.symm ▸ hv)
    refine ⟨i, ⟨e.1, heN⟩, ?_⟩
    rw [hleft i e]
    change elementaryCharacter (l i) (C.equiv e) ≠ 1
    rw [ne_eq, elementaryCharacter_eq_one_iff, hecoord]
    exact hlnz
  · intro N hN hnot i n
    exact hother i N hN hnot n

end SymmetricSubgroupAsymptotics.ZmudPrimarySocleCharacters
