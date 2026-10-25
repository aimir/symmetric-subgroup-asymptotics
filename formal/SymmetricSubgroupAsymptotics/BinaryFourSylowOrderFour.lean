import SymmetricSubgroupAsymptotics.BinaryFourUnitriangularSquares
import SymmetricSubgroupAsymptotics.BinaryFourLinearGroups
import SymmetricSubgroupAsymptotics.CFSGTypeAGoodSylow

/-! The actual unitriangular square-one bound forces order four in any
binary GL4 subgroup whose order is divisible by 32. The map into the fixed
unitriangular Sylow is constructed using genuine Sylow conjugacy. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.BinaryFourSylowOrderFour
open BinaryFourUnitriangularSquares

/-- The coordinate count is used through an actual injective homomorphism. -/
theorem exists_order_four_of_embedding {P : Type} [Group P] [Finite P]
    (f : P →* U) (hf : Function.Injective f) (hcard : 29 ≤ Nat.card P) :
    ∃ g : P, orderOf g = 4 := by
  obtain ⟨g,hg⟩ : ∃ g : P, g ^ 2 ≠ 1 := by
    by_contra hn
    push Not at hn
    let j : P → {u : U // u ^ 2 = 1} := fun g => ⟨f g,by rw [←map_pow,hn,map_one]⟩
    have hj : Function.Injective j := by
      intro x y h
      exact hf (congrArg Subtype.val h)
    have hle := (Nat.card_le_card_of_injective j hj).trans card_square_one_le
    omega
  have hfour : g ^ 4 = 1 := by
    apply hf
    rw [map_pow,map_one]
    exact pow_four (f g)
  refine ⟨g,?_⟩
  exact orderOf_eq_prime_pow (p := 2) (n := 1) (by simpa using hg) (by simpa using hfour)

/-- The original subgroup, with its original elements, contains order four. -/
theorem exists_order_four (H : Subgroup BinaryFourLinearGroups.General)
    (h32 : 32 ∣ Nat.card H) : ∃ g : H, orderOf g = 4 := by
  let P : Sylow 2 H := default
  let f : H →* BinaryFourLinearGroups.SL :=
    BinaryFourLinearGroups.specialGeneralEquiv.symm.toMonoidHom.comp H.subtype
  have hf : Function.Injective f :=
    BinaryFourLinearGroups.specialGeneralEquiv.symm.injective.comp Subtype.coe_injective
  obtain ⟨Q,hQ⟩ := P.exists_comap_eq_of_injective hf
  let j : P →* Q := (f.comp (P : Subgroup H).subtype).codRestrict Q (by
    intro x
    change x.val ∈ Q.comap f
    rw [hQ]
    exact x.property)
  have hj : Function.Injective j := by
    intro x y h
    apply Subtype.ext
    exact hf (congrArg Subtype.val h)
  let e := Q.equiv (CFSGTypeAGoodSylow.actualUpperSylow (ZMod 2) 2 4)
  let k : P →* U := e.toMonoidHom.comp j
  have hk : Function.Injective k := e.injective.comp hj
  have hc : 29 ≤ Nat.card P := by
    have hd : 2 ^ 5 ∣ Nat.card P := P.pow_dvd_card_of_pow_dvd_card h32
    have hh : 32 ≤ Nat.card P := Nat.le_of_dvd Nat.card_pos hd
    exact (show 29 ≤ 32 by decide).trans hh
  obtain ⟨g,hg⟩ := exists_order_four_of_embedding k hk hc
  refine ⟨g.val,?_⟩
  exact (orderOf_injective (P : Subgroup H).subtype Subtype.coe_injective g).trans hg

end SymmetricSubgroupAsymptotics.BinaryFourSylowOrderFour
