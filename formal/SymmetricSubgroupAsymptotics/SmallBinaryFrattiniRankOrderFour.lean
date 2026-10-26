import SymmetricSubgroupAsymptotics.PrimeFrattiniCardinality

/-! An actual two-group of order at most sixteen containing an actual
order-four element has prime-Frattini rank at most three. Full rank four
would make the actual Frattini subgroup trivial and kill every square. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.SmallBinaryFrattiniRankOrderFour

theorem rank_le_three {N : Type*} [Group N] [Finite N]
    (hN : IsPGroup 2 N) (hcard : Nat.card N ≤ 16)
    (x : N) (hx : orderOf x = 4) :
    Module.finrank (ZMod 2) (PrimeCharacters 2 N) ≤ 3 := by
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hpow : 2 ^ Module.finrank (ZMod 2) (PrimeCharacters 2 N) ≤ 2 ^ 4 :=
    (primeCharacters_pow_finrank_le_card 2 N).trans (by simpa using hcard)
  have hr : Module.finrank (ZMod 2) (PrimeCharacters 2 N) ≤ 4 :=
    (Nat.pow_le_pow_iff_right (by decide : 1 < (2 : ℕ))).mp hpow
  by_contra hnot
  have he : Module.finrank (ZMod 2) (PrimeCharacters 2 N) = 4 := by omega
  have hNcard : Nat.card N = 2 ^ 4 := by
    have hle := primeCharacters_pow_finrank_le_card 2 N
    rw [he] at hle
    omega
  have hPhi : Nat.card (frattini N) = 1 := by
    have hh := PrimeFrattiniCardinality.frattini_card 2 N hN 4 hNcard
    simpa only [he,Nat.sub_self,pow_zero] using hh
  letI : Subsingleton (frattini N) := (Nat.card_eq_one_iff_unique.mp hPhi).1
  have hsquare : x ^ 2 ∈ frattini N := by
    rw [← primeAbelianizationGroupMap_ker 2 N hN]
    change primeAbelianizationGroupMap 2 N (x ^ 2) = 1
    rw [map_pow]
    change (2 : ℕ) • primeAbelianizationMap 2 N (Additive.ofMul x) = 0
    exact ZModModule.char_nsmul_eq_zero 2 _
  have hone : (⟨x ^ 2,hsquare⟩ : frattini N) = 1 := Subsingleton.elim _ _
  have hxpow : x ^ 2 = 1 := congrArg (fun z : frattini N => z.val) hone
  have hd := orderOf_dvd_of_pow_eq_one hxpow
  rw [hx] at hd
  norm_num at hd

end SymmetricSubgroupAsymptotics.SmallBinaryFrattiniRankOrderFour
