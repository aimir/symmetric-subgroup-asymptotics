import SymmetricSubgroupAsymptotics.ScalarFourInvariantC4TwistedCount
import SymmetricSubgroupAsymptotics.Non2PreE7SaprimOddCyclicAffine

/-! A finite cyclic group killed by four embeds in one literal C4 column.
This is structural coordinate recognition, with no subgroup census. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CyclicExponentFourCoordinates
abbrev C4 := Multiplicative (ZMod 4)
variable (G : Type) [Group G] [Finite G]

 theorem exists_embedding (hcyc : IsCyclic G) (hfour : ∀ g : G,g^4=1) :
    ∃ j : G →* C4,Function.Injective j := by
  letI : IsCyclic G := hcyc
  obtain ⟨g,hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := G)
  have hd : Nat.card G∣4 := hg ▸ (orderOf_dvd_of_pow_eq_one (hfour g))
  have hp : 0<Nat.card G := Nat.card_pos
  have hl : Nat.card G≤4 := Nat.le_of_dvd (by decide) hd
  have hn3 : Nat.card G≠3 := by
    intro hn
    norm_num [hn] at hd
  have hc : Nat.card G=1 ∨ Nat.card G=2 ∨ Nat.card G=4 := by omega
  rcases hc with h1 | h2 | h4
  · letI : Subsingleton G := (Nat.card_eq_one_iff_unique.mp h1).1
    exact ⟨1,fun _ _ _ => Subsingleton.elim _ _⟩
  · let e : G ≃* Multiplicative (ZMod 2) :=
      (zmodCyclicMulEquiv hcyc).symm.trans
        (ZMod.ringEquivCongr h2).toAddEquiv.toMultiplicative
    exact ⟨binaryIntoC4.comp e.toMonoidHom,
      binaryIntoC4_injective.comp e.injective⟩
  · let e : G ≃* C4 := (zmodCyclicMulEquiv hcyc).symm.trans
      (ZMod.ringEquivCongr h4).toAddEquiv.toMultiplicative
    exact ⟨e.toMonoidHom,e.injective⟩

end SymmetricSubgroupAsymptotics.CyclicExponentFourCoordinates
