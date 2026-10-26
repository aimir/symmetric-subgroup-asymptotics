import SymmetricSubgroupAsymptotics.SmallBinaryFrattiniRankOrderFour
import SymmetricSubgroupAsymptotics.ElevenPointDoubleFourCentralizerCard
import SymmetricSubgroupAsymptotics.BinaryFrattiniSmallRankAutomorphismDivisor
import SymmetricSubgroupAsymptotics.FiniteNormalizerCardDivisor
import SymmetricSubgroupAsymptotics.BurnsideTwoPrimeSolvability
import SymmetricSubgroupAsymptotics.CFSGGoodSylowOfTwoPSubgroups
import Mathlib.Data.Nat.GCD.Basic

/-! Generic actual eleven-point action bridge. An order-four double
four-cycle in a Sylow two-subgroup bounds its Frattini rank; the actual
centralizer and automorphism divisors then force its normalizer order
to divide144 when the original group order divides7920. Burnside's
proved two-prime theorem gives solvability. No M11 model is identified. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.ElevenPointBinarySylowNormalizerSolvable

local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

private theorem two_prime_divisor_receipt :
    ∀ n : Fin 145, n.val ∣ 144 →
      ∃ a : Fin 5, ∃ b : Fin 3, n.val = 2 ^ a.val * 3 ^ b.val := by decide +kernel

theorem isSolvable_of_card_dvd_144 {K : Type*} [Group K] [Finite K]
    (hcard : Nat.card K ∣ 144) : IsSolvable K := by
  have hle := Nat.le_of_dvd (by decide : 0 < 144) hcard
  obtain ⟨a,b,he⟩ := two_prime_divisor_receipt ⟨Nat.card K,by omega⟩ hcard
  letI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact burnside_solvable (p := 2) (q := 3) (a := a.val) (b := b.val) he

variable {G : Type*} [Group G] [Finite G] [MulAction G (Fin 11)]
    [FaithfulSMul G (Fin 11)]

theorem centralizer_card_dvd_192 (P : Subgroup G) (y : G) (hy : y ∈ P)
    (htype : (MulAction.toPermHom G (Fin 11) y).cycleType = Multiset.replicate 2 4) :
    Nat.card (Subgroup.centralizer (P : Set G)) ∣ 192 := by
  let rho := MulAction.toPermHom G (Fin 11)
  let f : Subgroup.centralizer (P : Set G) →*
      Subgroup.centralizer ({rho y} : Set (Equiv.Perm (Fin 11))) := {
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
  rw [ElevenPointDoubleFourCentralizerCard.card (by simp) (rho y) htype] at hd
  exact hd

omit [MulAction G (Fin 11)] [FaithfulSMul G (Fin 11)] in
theorem sylow_card_le_sixteen (P : Sylow 2 G) (hcard : Nat.card G ∣ 7920) :
    Nat.card P ≤ 16 := by
  obtain ⟨a,ha⟩ := IsPGroup.iff_card.mp P.isPGroup'
  have hd : 2 ^ a ∣ 7920 := by
    rw [← ha]
    exact (P : Subgroup G).card_subgroup_dvd_card.trans hcard
  have ha4 : a ≤ 4 := by
    by_contra h
    have h32 : 32 ∣ 7920 := (Nat.pow_dvd_pow 2 (by omega : 5 ≤ a)).trans hd
    exact (by decide : ¬ 32 ∣ 7920) h32
  rw [ha]
  exact Nat.pow_le_pow_right (by decide : 0 < 2) ha4

theorem normalizer_card_dvd_144 (P : Sylow 2 G) (hcard : Nat.card G ∣ 7920)
    (y : G) (hy : y ∈ P) (horder : orderOf y = 4)
    (htype : (MulAction.toPermHom G (Fin 11) y).cycleType = Multiset.replicate 2 4) :
    Nat.card (Subgroup.normalizer (P : Set G)) ∣ 144 := by
  let yP : P := ⟨y,hy⟩
  have hyP : orderOf yP = 4 := (Subgroup.orderOf_coe yP).symm.trans horder
  have hr := SmallBinaryFrattiniRankOrderFour.rank_le_three
    P.isPGroup' (sylow_card_le_sixteen P hcard) yP hyP
  obtain ⟨a,ha⟩ := BinaryFrattiniSmallRankAutomorphismDivisor.automorphism_card_dvd P.isPGroup' hr
  have hC := centralizer_card_dvd_192 (P : Subgroup G) y hy htype
  have hd : Nat.card (Subgroup.normalizer (P : Set G)) ∣ 192 * (2 ^ a * 168) :=
    (normalizer_card_dvd_centralizer_mul_aut (P : Subgroup G)).trans (Nat.mul_dvd_mul hC ha)
  have hc : Nat.Coprime (192 * (2 ^ a * 168)) 55 := by
    rw [Nat.coprime_mul_iff_left,Nat.coprime_mul_iff_left]
    exact ⟨by decide,(by decide : Nat.Coprime 2 55).pow_left a,by decide⟩
  have hNcop : Nat.Coprime (Nat.card (Subgroup.normalizer (P : Set G))) 55 :=
    hc.coprime_dvd_left hd
  apply hNcop.dvd_mul_right.mp
  have hN := (Subgroup.normalizer (P : Set G)).card_subgroup_dvd_card.trans hcard
  simpa only [show (144 : ℕ) * 55 = 7920 by decide] using hN

theorem normalizer_isSolvable (P : Sylow 2 G) (hcard : Nat.card G ∣ 7920)
    (y : G) (hy : y ∈ P) (horder : orderOf y = 4)
    (htype : (MulAction.toPermHom G (Fin 11) y).cycleType = Multiset.replicate 2 4) :
    IsSolvable (Subgroup.normalizer (P : Set G)) :=
  isSolvable_of_card_dvd_144 (normalizer_card_dvd_144 P hcard y hy horder htype)

theorem goodSylowPrime_of_two_p_subgroups (U : Subgroup G) (hU : IsPGroup 2 U)
    (hcard : Nat.card G ∣ 7920) (y : G) (horder : orderOf y = 4)
    (htype : (MulAction.toPermHom G (Fin 11) y).cycleType = Multiset.replicate 2 4)
    (hgen : U ⊔ Subgroup.zpowers y = ⊤) : CFSGReduction.GoodSylowPrime G 2 := by
  have hV : IsPGroup 2 (Subgroup.zpowers y) := by
    apply IsPGroup.of_card (n := 2)
    rw [Nat.card_zpowers,horder]
    norm_num
  obtain ⟨P,hP⟩ := hV.exists_le_sylow
  have hy : y ∈ P := hP (Subgroup.mem_zpowers y)
  exact CFSGReduction.goodSylowPrime_of_two_p_subgroups_and_exists_soluble_normalizer
    U (Subgroup.zpowers y) hU hV hgen
    ⟨P,normalizer_isSolvable P hcard y hy horder htype⟩

end SymmetricSubgroupAsymptotics.ElevenPointBinarySylowNormalizerSolvable
