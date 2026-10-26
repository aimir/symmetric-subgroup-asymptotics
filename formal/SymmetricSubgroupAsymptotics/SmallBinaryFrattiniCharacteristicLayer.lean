import SymmetricSubgroupAsymptotics.PrimeFrattiniCardinality

/-! A finite two-group of order eight with smaller prime quotient has
a genuine characteristic subgroup of order two. Rank two uses the
actual Frattini subgroup. Rank one uses fourth powers in the actual
cyclic group, derived from the original single generating lift. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.SmallBinaryFrattiniCharacteristicLayer

variable (p : ℕ) [Fact p.Prime] {N : Type*} [Group N] [Finite N]

theorem card_eq_one_of_rank_zero (hN : IsPGroup p N)
    (hr : Module.finrank (ZMod p) (PrimeCharacters p N)=0) : Nat.card N=1 := by
  have ht : ∃ g : Fin (Module.finrank (ZMod p) (PrimeCharacters p N)) → N,
      Subgroup.closure (Set.range g)=⊤ := exists_primeFrattini_generating_tuple p hN
  rw [hr] at ht
  obtain ⟨g,hg⟩ := ht
  have he : (⊥ : Subgroup N)=⊤ := by
    simpa only [Set.range_eq_empty,Subgroup.closure_empty] using hg
  have hc := congrArg (fun H : Subgroup N => Nat.card H) he
  simpa only [Subgroup.card_bot,Subgroup.card_top] using hc.symm

theorem isCyclic_of_rank_one (hN : IsPGroup p N)
    (hr : Module.finrank (ZMod p) (PrimeCharacters p N)=1) : IsCyclic N := by
  have ht : ∃ g : Fin (Module.finrank (ZMod p) (PrimeCharacters p N)) → N,
      Subgroup.closure (Set.range g)=⊤ := exists_primeFrattini_generating_tuple p hN
  rw [hr] at ht
  obtain ⟨g,hg⟩ := ht
  have hrg : Set.range g={g 0} := by
    ext n
    constructor
    · rintro ⟨i,rfl⟩
      have hi : i=0 := Subsingleton.elim _ _
      rw [hi]
      exact Set.mem_singleton _
    · intro hn
      exact ⟨0,(Set.mem_singleton_iff.mp hn).symm⟩
  apply isCyclic_iff_exists_zpowers_eq_top.mpr
  refine ⟨g 0,?_⟩
  rw [Subgroup.zpowers_eq_closure,← hrg]
  exact hg

omit p in
theorem exists_characteristic_two_of_cyclic_eight [IsCyclic N]
    (hcard : Nat.card N=8) :
    ∃ Z : Subgroup N, Z.Characteristic ∧ Nat.card Z=2 := by
  letI : CommGroup N := IsCyclic.commGroup
  obtain ⟨g,hg⟩ := isCyclic_iff_exists_zpowers_eq_top.mp (inferInstance : IsCyclic N)
  let Z : Subgroup N := (powMonoidHom 4 : N →* N).range
  have hZ : Z=Subgroup.zpowers (g^4) := by
    change (powMonoidHom 4 : N →* N).range=Subgroup.zpowers (g^4)
    rw [MonoidHom.range_eq_map,← hg,MonoidHom.map_zpowers]
    rfl
  refine ⟨Z,?_,?_⟩
  · apply Subgroup.characteristic_iff_map_le.mpr
    intro a x hx
    obtain ⟨y,hy,rfl⟩ := hx
    change ∃ n : N, n^4=y at hy
    obtain ⟨n,rfl⟩ := hy
    exact ⟨a n,(map_pow a n 4).symm⟩
  · rw [hZ,Nat.card_zpowers,orderOf_pow,orderOf_eq_card_of_zpowers_eq_top hg,hcard]
    decide

omit p in
theorem exists_characteristic_two_of_rank_le_two (hN : IsPGroup 2 N)
    (hcard : Nat.card N=8)
    (hr : Module.finrank (ZMod 2) (PrimeCharacters 2 N)≤2) :
    ∃ Z : Subgroup N, Z.Characteristic ∧ Nat.card Z=2 := by
  have hr0 : Module.finrank (ZMod 2) (PrimeCharacters 2 N)≠0 := by
    intro he
    have hc := card_eq_one_of_rank_zero 2 hN he
    omega
  by_cases hr1 : Module.finrank (ZMod 2) (PrimeCharacters 2 N)=1
  · letI : IsCyclic N := isCyclic_of_rank_one 2 hN hr1
    exact exists_characteristic_two_of_cyclic_eight hcard
  · have hr2 : Module.finrank (ZMod 2) (PrimeCharacters 2 N)=2 := by omega
    refine ⟨frattini N,inferInstance,?_⟩
    have hc := PrimeFrattiniCardinality.frattini_card 2 N hN 3
      (by simpa only [show (2:ℕ)^3=8 by decide] using hcard)
    simpa only [hr2,show 3-2=1 by decide,pow_one] using hc

end SymmetricSubgroupAsymptotics.SmallBinaryFrattiniCharacteristicLayer
