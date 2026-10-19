import SymmetricSubgroupAsymptotics.MarkedC4ProductEncoding
import Mathlib.GroupTheory.OrderOfElement

/-! The actual odd factor has trivial C4 characters. This supplies the
Hom comparison in a physical product code; odd configurations must still
remain in its finite index or be counted separately. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.MarkedC4.CoprimeProductCharacters

abbrev C4 := Multiplicative (ZMod 4)

theorem hom_eq_one {O : Type} [Group O]
    (hodd : Nat.Coprime (Nat.card O) 4) (f : O →* C4) (o : O) : f o=1 := by
  apply orderOf_eq_one_iff.mp
  apply Nat.eq_one_of_dvd_coprimes hodd
  · exact (orderOf_map_dvd f o).trans (orderOf_dvd_natCard o)
  · simpa using orderOf_dvd_natCard (f o)

/-- Restriction is injective because the other ACTUAL direct factor has
order coprime to four; no character-extension claim is needed. -/
theorem restriction_injective {P O : Type} [Group P] [Group O]
    (hodd : Nat.Coprime (Nat.card O) 4) :
    Function.Injective (fun f : P × O →* C4 => f.comp (MonoidHom.inl P O)) := by
  intro f g he
  apply MonoidHom.ext
  rintro ⟨p,o⟩
  have hf : f (1,o)=1 := hom_eq_one hodd (f.comp (MonoidHom.inr P O)) o
  have hg : g (1,o)=1 := hom_eq_one hodd (g.comp (MonoidHom.inr P O)) o
  have hp : f (p,1)=g (p,1) := congrArg (fun k : P →* C4 => k p) he
  have hx : (p,o)=(p,1)*(1,o) := by simp
  rw [hx,map_mul,map_mul,hf,hg,hp]

/-- Actual coprime product charts preserve every C4 mark at the binary
factor, regardless of the number of different odd configurations. -/
theorem card_hom_le_of_split {G P O : Type} [Group G] [Group P] [Group O]
    [Finite P] [Finite O] (e : G ≃* P × O)
    (hodd : Nat.Coprime (Nat.card O) 4) :
    Nat.card (G →* C4)≤Nat.card (P →* C4) := by
  have hcard : Nat.card (G →* C4)=Nat.card (P × O →* C4) :=
    (Nat.card_congr (homPrecompEquiv e)).symm
  rw [hcard]
  exact Nat.card_le_card_of_injective _ (restriction_injective hodd)

end SymmetricSubgroupAsymptotics.MarkedC4.CoprimeProductCharacters
