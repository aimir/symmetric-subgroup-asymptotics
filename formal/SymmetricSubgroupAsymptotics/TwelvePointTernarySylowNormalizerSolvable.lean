import SymmetricSubgroupAsymptotics.PrimeFrattiniSmallRankAutomorphismDivisor
import SymmetricSubgroupAsymptotics.FiniteNormalizerCardDivisor
import SymmetricSubgroupAsymptotics.BurnsideTwoPrimeSolvability
import SymmetricSubgroupAsymptotics.CFSGGoodSylowOfTwoPSubgroups
import Mathlib.GroupTheory.Perm.Centralizer
import Mathlib.NumberTheory.Divisors

/-! A faithful twelve-point action and a fixed-point-free order-three
permutation suffice to make a containing Sylow-three normalizer soluble
when the source order divides95040. The Frattini image and the literal
permutation centralizer retain the same prime divisors throughout. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.TwelvePointTernarySylowNormalizerSolvable
local instance : Fact (Nat.Prime 3) := ⟨by decide⟩

private theorem two_prime_divisor_receipt :
    ∀ n ∈ Nat.divisors 1728,
      ∃ a : Fin 7, ∃ b : Fin 4, n = 2 ^ a.val * 3 ^ b.val := by decide +kernel

theorem isSolvable_of_card_dvd_1728 {K : Type*} [Group K] [Finite K]
    (hcard : Nat.card K ∣ 1728) : IsSolvable K := by
  obtain ⟨a,b,he⟩ := two_prime_divisor_receipt (Nat.card K)
    (Nat.mem_divisors.mpr ⟨hcard,by decide⟩)
  letI : Fact (Nat.Prime 2) := ⟨by decide⟩
  exact burnside_solvable (p := 2) (q := 3) (a := a.val) (b := b.val) he

variable {G : Type*} [Group G] [Finite G] [MulAction G (Fin 12)]
    [FaithfulSMul G (Fin 12)]

theorem centralizer_card_dvd_1944 (P : Subgroup G) (y : G) (hy : y ∈ P)
    (htype : (MulAction.toPermHom G (Fin 12) y).cycleType = Multiset.replicate 4 3) :
    Nat.card (Subgroup.centralizer (P : Set G)) ∣ 1944 := by
  let rho := MulAction.toPermHom G (Fin 12)
  let f : Subgroup.centralizer (P : Set G) →*
      Subgroup.centralizer ({rho y} : Set (Equiv.Perm (Fin 12))) := {
    toFun := fun x => ⟨rho x.val,by
      apply Subgroup.mem_centralizer_singleton_iff.mpr
      have hh := Subgroup.mem_centralizer_iff.mp x.property y hy
      simpa only [← map_mul] using (congrArg rho hh).symm⟩
    map_one' := Subtype.ext rho.map_one
    map_mul' x z := Subtype.ext (rho.map_mul x.val z.val) }
  have hf : Function.Injective f := by
    intro x z h
    apply Subtype.ext
    exact MulAction.toPerm_injective (congrArg Subtype.val h)
  have hd := Subgroup.card_dvd_of_injective f hf
  have hc : Nat.card (Subgroup.centralizer ({rho y} : Set (Equiv.Perm (Fin 12)))) = 1944 := by
    rw [Equiv.Perm.nat_card_centralizer,htype]
    norm_num
  rwa [hc] at hd

omit [MulAction G (Fin 12)] [FaithfulSMul G (Fin 12)] in
theorem sylow_rank_le_three (P : Sylow 3 G) (hcard : Nat.card G ∣ 95040) :
    Module.finrank (ZMod 3) (PrimeCharacters 3 P) ≤ 3 := by
  obtain ⟨a,ha⟩ := IsPGroup.iff_card.mp P.isPGroup'
  have hd : 3 ^ a ∣ 95040 := by
    rw [← ha]
    exact (P : Subgroup G).card_subgroup_dvd_card.trans hcard
  have ha3 : a ≤ 3 := by
    by_contra h
    have h81 : 81 ∣ 95040 := (Nat.pow_dvd_pow 3 (by omega : 4 ≤ a)).trans hd
    exact (by decide : ¬ 81 ∣ 95040) h81
  have hr : Module.finrank (ZMod 3) (PrimeCharacters 3 P) ≤ a := by
    apply (Nat.pow_le_pow_iff_right (by decide : 1 < 3)).mp
    exact (primeCharacters_pow_finrank_le_card 3 P).trans_eq ha
  exact hr.trans ha3

theorem normalizer_card_dvd_1728 (P : Sylow 3 G) (hcard : Nat.card G ∣ 95040)
    (y : G) (hy : y ∈ P)
    (htype : (MulAction.toPermHom G (Fin 12) y).cycleType = Multiset.replicate 4 3) :
    Nat.card (Subgroup.normalizer (P : Set G)) ∣ 1728 := by
  obtain ⟨a,ha⟩ := PrimeFrattiniSmallRankAutomorphismDivisor.ternary_automorphism_card_dvd
    P.isPGroup' (sylow_rank_le_three P hcard)
  have hC := centralizer_card_dvd_1944 (P : Subgroup G) y hy htype
  have hd : Nat.card (Subgroup.normalizer (P : Set G)) ∣ 1944 * (3 ^ a * 11232) :=
    (normalizer_card_dvd_centralizer_mul_aut (P : Subgroup G)).trans (Nat.mul_dvd_mul hC ha)
  have hc : Nat.Coprime (1944 * (3 ^ a * 11232)) 55 := by
    rw [Nat.coprime_mul_iff_left,Nat.coprime_mul_iff_left]
    exact ⟨by decide,(by decide : Nat.Coprime 3 55).pow_left a,by decide⟩
  have hNcop : Nat.Coprime (Nat.card (Subgroup.normalizer (P : Set G))) 55 :=
    hc.coprime_dvd_left hd
  apply hNcop.dvd_mul_right.mp
  have hN := (Subgroup.normalizer (P : Set G)).card_subgroup_dvd_card.trans hcard
  simpa only [show (1728 : ℕ) * 55 = 95040 by decide] using hN

theorem normalizer_isSolvable (P : Sylow 3 G) (hcard : Nat.card G ∣ 95040)
    (y : G) (hy : y ∈ P)
    (htype : (MulAction.toPermHom G (Fin 12) y).cycleType = Multiset.replicate 4 3) :
    IsSolvable (Subgroup.normalizer (P : Set G)) :=
  isSolvable_of_card_dvd_1728 (normalizer_card_dvd_1728 P hcard y hy htype)

theorem goodSylowPrime_of_two_p_subgroups (U : Subgroup G) (hU : IsPGroup 3 U)
    (hcard : Nat.card G ∣ 95040) (y : G) (horder : orderOf y = 3)
    (htype : (MulAction.toPermHom G (Fin 12) y).cycleType = Multiset.replicate 4 3)
    (hgen : U ⊔ Subgroup.zpowers y = ⊤) : CFSGReduction.GoodSylowPrime G 3 := by
  have hV : IsPGroup 3 (Subgroup.zpowers y) := by
    apply IsPGroup.of_card (n := 1)
    rw [Nat.card_zpowers,horder]
    norm_num
  obtain ⟨P,hP⟩ := hV.exists_le_sylow
  have hy : y ∈ P := hP (Subgroup.mem_zpowers y)
  exact CFSGReduction.goodSylowPrime_of_two_p_subgroups_and_exists_soluble_normalizer
    U (Subgroup.zpowers y) hU hV hgen
    ⟨P,normalizer_isSolvable P hcard y hy htype⟩

end SymmetricSubgroupAsymptotics.TwelvePointTernarySylowNormalizerSolvable
