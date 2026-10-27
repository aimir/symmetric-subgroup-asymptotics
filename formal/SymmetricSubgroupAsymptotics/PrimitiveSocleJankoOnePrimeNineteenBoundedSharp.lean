import SymmetricSubgroupAsymptotics.CFSGJankoOneSelectedPrimeNineteen
import SymmetricSubgroupAsymptotics.PrimitiveSocleLargePrimePairBoundedSharp

/-! A selected vector period in a genuine representation of the ORIGINAL
J1 presentation supplies prime19 in the SAME original simple factor.
The existing pair/normalizer theorem pays its bounded primitive branch;
prime19 excludes a nonaffine component of degree at most10. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.PrimitiveSocleJankoOnePrimeNineteenBoundedSharp
open PrimitiveSocleRawStructure CFSGReduction TraceySharpHalfDegreeNumerics

 theorem simple_nineteen_dvd
    {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X] [FaithfulSMul G X]
    (D : NonaffineData G X)
    (e : D.Simple ≃* CFSG.Models.Presentations.J1.Model) :
    19 ∣ Nat.card D.Simple := by
  letI : Finite CFSG.Models.Presentations.J1.Model := Finite.of_equiv D.Simple e.toEquiv
  rw [Nat.card_congr e.toEquiv]
  exact CFSGJankoOneSelectedPrimeNineteen.nineteen_dvd_card

 theorem genRank_le_sharpFloor_of_jankoOne
    {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X] [FaithfulSMul G X]
    (D : NonaffineData G X) (hCFSG : CFSG.CFSGClassification) (hhi : Nat.card X ≤ 21)
    (e : D.Simple ≃* CFSG.Models.Presentations.J1.Model) :
    MarkedC4.genRank G ≤ sharpFloor (Nat.card X) := by
  obtain ⟨S,hS,hcard⟩ := CFSGGeneration.of_mulEquiv e.symm CFSGGeneration.j1_twoGenerated
  exact PrimitiveSocleLargePrimePairBoundedSharp.genRank_le_sharpFloor_of_prime
    D hCFSG hhi 19 (by decide) (by decide) (simple_nineteen_dvd D e)
      ((MarkedC4.genRank_le hS).trans hcard)

 theorem not_jankoOne_of_degree_le_ten
    {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X] [FaithfulSMul G X]
    (D : NonaffineData G X) (hsmall : Nat.card X ≤ 10)
    (e : D.Simple ≃* CFSG.Models.Presentations.J1.Model) : False := by
  have hd := PrimitiveSocleElevenPointTitsExclusion.simple_card_dvd_degree_factorial D
  have h19 : 19 ≤ Nat.card X := (show Nat.Prime 19 by decide).dvd_factorial.mp
    ((simple_nineteen_dvd D e).trans hd)
  omega

end SymmetricSubgroupAsymptotics.PrimitiveSocleJankoOnePrimeNineteenBoundedSharp
