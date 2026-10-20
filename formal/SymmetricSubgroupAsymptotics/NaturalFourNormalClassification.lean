import SymmetricSubgroupAsymptotics.NaturalThreeNormalClassification

/-! The literal S4 normal menu, obtained through its genuine pairing
quotient and the checked self-centralizing Klein subgroup. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.NaturalFourNormalClassification

private theorem pairing_even : ∀ p : Equiv.Perm (Fin 4),
    Equiv.Perm.sign (NaturalS4.pairing p)=Equiv.Perm.sign p := by decide +kernel

private theorem preimage_alternating :
    (alternatingGroup (Fin 3)).comap NaturalS4.pairing=alternatingGroup (Fin 4) := by
  ext p
  change Equiv.Perm.sign (NaturalS4.pairing p)=1 ↔ Equiv.Perm.sign p=1
  rw [pairing_even]

theorem normal_four_cases (N : Subgroup (Equiv.Perm (Fin 4))) (hN : N.Normal) :
    N=⊥ ∨ N=NaturalS4.klein ∨ N=alternatingGroup (Fin 4) ∨ N=⊤ := by
  by_cases hn : N=⊥
  · exact Or.inl hn
  letI : N.Normal := hN
  have hk : NaturalS4.pairing.ker≤N := by
    rw [NaturalS4.ker_pairing]
    exact le_of_minimal_selfCentralizing NaturalS4.klein NaturalS4.klein_minimal
      NaturalS4.klein_selfCentralizing N hn
  have he : N=(N.map NaturalS4.pairing).comap NaturalS4.pairing :=
    (Subgroup.comap_map_eq_self hk).symm
  have hm := hN.map NaturalS4.pairing NaturalS4.pairing_surjective
  rcases NaturalThreeNormalClassification.normal_trichotomy
      (N.map NaturalS4.pairing) hm with hb | ha | ht
  · right; left
    rw [he,hb]
    exact NaturalS4.ker_pairing
  · right; right; left
    rw [he,ha,preimage_alternating]
  · right; right; right
    rw [he,ht,Subgroup.comap_top]

end SymmetricSubgroupAsymptotics.NaturalFourNormalClassification
