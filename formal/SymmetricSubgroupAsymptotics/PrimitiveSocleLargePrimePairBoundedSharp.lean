import SymmetricSubgroupAsymptotics.LargePrimeSocleQuotientGenerators
import SymmetricSubgroupAsymptotics.BoundedSharpMathieuAndJFourExcludedActualResidual

/-! A genuine prime>=11 in the original paired simple factor pays all
bounded sharp degrees<=21 through the actual Sylow normalizer quotient.
The shared installer applies to checked J3/He/HS/McL divisors and pairs;
no outer order or expected model order is used. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.PrimitiveSocleLargePrimePairBoundedSharp
open PrimitiveSocleRawStructure CFSGReduction TraceySharpHalfDegreeNumerics
open TenPointHalfDegreeCompleteCFSG (fixedBudget)

private theorem fixed_budget_pays (n p : ℕ) (hlo : 11 ≤ n) (hhi : n ≤ 21) (hp : 11 ≤ p) :
    3+fixedBudget (n-p) ≤ sharpFloor n := by
  by_cases h16 : n ≤ 16
  · have hb : fixedBudget (n-p) ≤ 2 := by unfold fixedBudget; split_ifs <;> omega
    exact (by omega : 3+fixedBudget (n-p) ≤ 5).trans
      (PrimitiveBoundedSharpElevenToTwentyOneCFSGReduction.five_le_sharpFloor_of_band n hlo hhi)
  by_cases h18 : n ≤ 18
  · have hb : fixedBudget (n-p) ≤ 3 := by unfold fixedBudget; split_ifs <;> omega
    exact (by omega : 3+fixedBudget (n-p) ≤ 6).trans
      (OriginalNonaffineBoundedSharpCFSGReduction.six_le_sharpFloor_of_band n (by omega) hhi)
  by_cases h20 : n ≤ 20
  · have hb : fixedBudget (n-p) ≤ 4 := by unfold fixedBudget; split_ifs <;> omega
    have hseven : 7 ≤ sharpFloor n :=
      TinyPrimeTopSharpFloorNumerics.le_sharpFloor_of_square n 7 5 (by omega)
        (TinyPrimeTopSharpFloorNumerics.log_le_of_pow n 5 (by omega) (by norm_num; omega))
        (by
          have hh := Nat.pow_le_pow_left (show 19 ≤ n by omega) 2
          norm_num at hh ⊢
          omega)
    exact (by omega : 3+fixedBudget (n-p) ≤ 7).trans hseven
  · have hn : n=21 := by omega
    have hb : fixedBudget (n-p) ≤ 5 := by unfold fixedBudget; split_ifs <;> omega
    exact (by omega : 3+fixedBudget (n-p) ≤ 8).trans
      (by simpa only [hn] using TinyPrimeTopSharpFloorNumerics.eight_le_sharpFloor_twenty_one)

/-- Generic original-D installer: prime divisibility and actual head2
are proved inputs, not outer/order/degree catalogue assumptions. -/
theorem genRank_le_sharpFloor_of_prime
    {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X] [FaithfulSMul G X]
    (D : NonaffineData G X) (hCFSG : CFSG.CFSGClassification) (hhi : Nat.card X ≤ 21)
    (p : ℕ) (hp : p.Prime) (hplo : 11 ≤ p) (hpdiv : p ∣ Nat.card D.Simple)
    (hhead : MarkedC4.genRank D.Simple ≤ 2) :
    MarkedC4.genRank G ≤ sharpFloor (Nat.card X) := by
  letI : Fact p.Prime := ⟨hp⟩
  have hd := PrimitiveSocleElevenPointTitsExclusion.simple_card_dvd_degree_factorial D
  have hple : p ≤ Nat.card X := hp.dvd_factorial.mp (hpdiv.trans hd)
  have hnot : ¬p^2 ∣ Nat.card D.Simple := by
    have htable : ∀ q : Fin 22, q.val.Prime → 11 ≤ q.val → ¬q.val^2 ∣ Nat.factorial 21 := by
      decide +kernel
    intro hh
    exact htable ⟨p,by omega⟩ hp hplo
      (hh.trans (hd.trans (Nat.factorial_dvd_factorial hhi)))
  have hb := LargePrimeSocleQuotientGenerators.nonaffine_genRank_le_fixedBudget
    (p := p) (X := X) hCFSG D (by omega) hhead hpdiv hnot (by omega) (by omega)
  exact hb.trans (fixed_budget_pays (Nat.card X) p (by omega) hhi hplo)

def LargePrimePairTag : CFSG.Sporadic → Prop
  | .j3 | .he | .hs | .mcl => True
  | _ => False

def selectedPrime : CFSG.Sporadic → ℕ
  | .j3 => 19
  | .he => 17
  | .hs | .mcl => 11
  | _ => 0

theorem model_prime (s : CFSG.Sporadic) (hs : LargePrimePairTag s)
    (hn : ¬IsMulCommutative s.Model) :
    (selectedPrime s).Prime ∧ 11 ≤ selectedPrime s ∧ selectedPrime s ∣ Nat.card s.Model := by
  cases s <;> try exact False.elim hs
  case j3 => exact ⟨by decide,by decide,CFSGSporadicPrimeProductDivisors.j3_prime_dvd_order hn⟩
  case he => exact ⟨by decide,by decide,CFSGSporadicPrimeProductDivisors.he_prime_dvd_order hn⟩
  case hs => exact ⟨by decide,by decide,CFSGSporadicPrimeProductDivisors.hs_prime_dvd_order hn⟩
  case mcl => exact ⟨by decide,by decide,CFSGSporadicPrimeProductDivisors.mcl_prime_dvd_order hn⟩

theorem model_pair (s : CFSG.Sporadic) (hs : LargePrimePairTag s) :
    CFSGGeneration.TwoGenerated s.Model := by
  cases s <;> try exact False.elim hs
  case j3 => exact CFSGGeneration.j3_twoGenerated
  case he => exact CFSGGeneration.he_twoGenerated
  case hs => exact CFSGGeneration.hs_twoGenerated
  case mcl => exact CFSGGeneration.mcl_twoGenerated

theorem genRank_le_sharpFloor_of_model
    {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X] [FaithfulSMul G X]
    (D : NonaffineData G X) (hCFSG : CFSG.CFSGClassification) (hhi : Nat.card X ≤ 21)
    (s : CFSG.Sporadic) (hs : LargePrimePairTag s) (e : D.Simple ≃* s.Model) :
    MarkedC4.genRank G ≤ sharpFloor (Nat.card X) := by
  have hn : ¬IsMulCommutative s.Model := fun hc =>
    D.noncommutative ((isMulCommutative_congr e).mpr hc)
  obtain ⟨hp,hplo,hpdiv⟩ := model_prime s hs hn
  have hd : selectedPrime s ∣ Nat.card D.Simple := by
    rw [Nat.card_congr e.toEquiv]
    exact hpdiv
  obtain ⟨S,hS,hcard⟩ := CFSGGeneration.of_mulEquiv e.symm (model_pair s hs)
  exact genRank_le_sharpFloor_of_prime D hCFSG hhi (selectedPrime s) hp hplo hd
    ((MarkedC4.genRank_le hS).trans hcard)

end SymmetricSubgroupAsymptotics.PrimitiveSocleLargePrimePairBoundedSharp
