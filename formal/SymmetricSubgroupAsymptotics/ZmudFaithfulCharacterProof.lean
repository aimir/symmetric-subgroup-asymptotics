import SymmetricSubgroupAsymptotics.ZmudAbelianSocleEnvelopes
import SymmetricSubgroupAsymptotics.ZmudNonabelianSocleQuotient

/-! Zmud's finite complex faithful-character tuple statement, proved from
actual socle normal generators. The primary semisimple dual supplies the
abelian detectors; one quotient detector handles all nonabelian minimal
normal subgroups. Tensoring and injected irreducible constituent selection
retain both families' fixed-space exclusions. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics

/-- The exact retained Zmud interface, with no additional premise. -/
theorem zmudFaithfulCharacterTupleInput_proved : ZmudFaithfulCharacterTupleInput := by
  intro G _ _ t ht
  obtain ⟨E, hEabelian, hEnonabelian⟩ :=
    ZmudAbelianSocleEnvelopes.exists_envelopes ht
  obtain ⟨F, hFabelian, hFnonabelian⟩ :=
    ZmudNonabelianSocleQuotient.exists_envelope (G := G)
  let T := fun i : Fin t => ZmudTensorFixedSpaces.tensor (E i) F
  apply ZmudFixedSpaceConstituents.exists_jointly_faithful_irreducibles t T
  intro N hN
  by_cases hc : IsMulCommutative N
  · obtain ⟨i, hi⟩ := hEabelian N hN hc
    refine ⟨i, ?_⟩
    exact ZmudTensorFixedSpaces.fixedFree_left (E i).action F.action N hi
      (hFabelian N hN hc)
  · have htne : t ≠ 0 := by
      intro hzero
      subst t
      obtain ⟨x, hx⟩ := ht
      have hrange : Set.range x = ∅ := by simp
      have hsocle : finiteGroupSocle G = ⊥ := by
        rw [← hx, hrange]
        simp
      apply hN.2.1
      apply le_antisymm ?_ bot_le
      intro n hn
      have hm : n ∈ finiteGroupSocle G :=
        Subgroup.subset_normalClosure ⟨N, hN, hn⟩
      rw [hsocle] at hm
      exact hm
    let i : Fin t := ⟨0, Nat.pos_of_ne_zero htne⟩
    refine ⟨i, ?_⟩
    exact ZmudTensorFixedSpaces.fixedFree_right (E i).action F.action N
      (hEnonabelian N hN hc i) (hFnonabelian N hN hc)

end SymmetricSubgroupAsymptotics
