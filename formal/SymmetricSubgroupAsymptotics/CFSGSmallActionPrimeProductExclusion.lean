import SymmetricSubgroupAsymptotics.CFSGSporadicPrimeProductDivisors
import SymmetricSubgroupAsymptotics.CFSGJ4TwentyThreeDivisor

/-! Literal prime-product divisors exclude nine named sporadic models
from actual simple socle factors in faithful actions on at most ten
points. Eight divisors come from the shared generating-pair theorem;
the already checked three-generator J4 divisor supplies the ninth.
All other sporadic tags remain explicit. No order table is used. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGSmallActionPrimeProductExclusion
open PrimitiveSocleRawStructure

def Excluded : CFSG.Sporadic → Prop
  | .m11 | .m12 | .m23 | .m24 | .j3 | .hs | .mcl | .he | .j4 => True
  | _ => False

theorem prime_divisor_above_ten (s : CFSG.Sporadic) (hs : Excluded s)
    (hn : ¬IsMulCommutative s.Model) :
    ∃ p : ℕ, p.Prime ∧ 10 < p ∧ p ∣ Nat.card s.Model := by
  cases s with
  | m11 => exact ⟨11,by decide,by decide,CFSGSporadicPrimeProductDivisors.m11_prime_dvd_order hn⟩
  | m12 => exact ⟨11,by decide,by decide,CFSGSporadicPrimeProductDivisors.m12_prime_dvd_order hn⟩
  | m22 => exact hs.elim
  | m23 => exact ⟨23,by decide,by decide,CFSGSporadicPrimeProductDivisors.m23_prime_dvd_order hn⟩
  | m24 => exact ⟨23,by decide,by decide,CFSGSporadicPrimeProductDivisors.m24_prime_dvd_order hn⟩
  | j1 => exact hs.elim
  | j2 => exact hs.elim
  | j3 => exact ⟨19,by decide,by decide,CFSGSporadicPrimeProductDivisors.j3_prime_dvd_order hn⟩
  | j4 => exact ⟨23,by decide,by decide,CFSGJ4TwentyThreeDivisor.twenty_three_dvd_order hn⟩
  | co1 => exact hs.elim
  | co2 => exact hs.elim
  | co3 => exact hs.elim
  | fi22 => exact hs.elim
  | fi23 => exact hs.elim
  | fi24Prime => exact hs.elim
  | hs => exact ⟨11,by decide,by decide,CFSGSporadicPrimeProductDivisors.hs_prime_dvd_order hn⟩
  | mcl => exact ⟨11,by decide,by decide,CFSGSporadicPrimeProductDivisors.mcl_prime_dvd_order hn⟩
  | he => exact ⟨17,by decide,by decide,CFSGSporadicPrimeProductDivisors.he_prime_dvd_order hn⟩
  | ru => exact hs.elim
  | suz => exact hs.elim
  | onan => exact hs.elim
  | hn => exact hs.elim
  | ly => exact hs.elim
  | th => exact hs.elim
  | babyMonster => exact hs.elim
  | monster => exact hs.elim

theorem not_excluded_of_degree_le_ten
    {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]
    [FaithfulSMul G X] (D : NonaffineData G X) (s : CFSG.Sporadic)
    (e : D.Simple ≃* s.Model) (hdegree : Nat.card X ≤ 10) : ¬Excluded s := by
  intro hs
  have hnc : ¬IsMulCommutative s.Model := by
    intro hc
    exact D.noncommutative ((CFSGReduction.isMulCommutative_congr e).mpr hc)
  obtain ⟨p,hp,hpten,hpdiv⟩ := prime_divisor_above_ten s hs hnc
  have hd := PrimitiveSocleElevenPointTitsExclusion.simple_card_dvd_degree_factorial D
  rw [Nat.card_congr e.toEquiv] at hd
  have hple : p ≤ Nat.card X := hp.dvd_factorial.mp (hpdiv.trans hd)
  omega

end SymmetricSubgroupAsymptotics.CFSGSmallActionPrimeProductExclusion
