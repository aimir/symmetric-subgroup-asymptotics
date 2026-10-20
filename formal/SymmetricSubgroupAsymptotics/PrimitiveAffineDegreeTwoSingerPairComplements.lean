import SymmetricSubgroupAsymptotics.ScalarPairSwapWreathImage
import SymmetricSubgroupAsymptotics.TernarySwapUpperNormalGenerators
import SymmetricSubgroupAsymptotics.ZModPowerHom
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairedEightRow19LinearWreath
import SymmetricSubgroupAsymptotics.C2WreathGeneration

/-! Exact paired Singer complements inside the checked order21 local
linear wreath. The two possibilities retain identical or inverse ternary
coordinates. Their actual images have uniform normal width two. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace PrimitiveAffineDegreeTwoSingerPairComplements

open SemidirectProduct
open PrimitiveAffineDegreeTwoPairedEightAffineTops

abbrev R := PrimitiveAffineDegreeTwoPairedEightRow19LinearWreath.R
abbrev s := PrimitiveAffineDegreeTwoPairedEightRow19LinearWreath.singerElement
abbrev f := PrimitiveAffineDegreeTwoPairedEightRow19LinearWreath.frobeniusElement
abbrev Ternary := TernarySwapUpperNormalGenerators.Ternary
abbrev Binary := TernarySwapUpperNormalGenerators.Binary
abbrev Plane := Fin 2 → ZMod 7

local instance : Fact (Nat.Prime 7) := ⟨by decide⟩

def scalarTwo : (ZMod 7)ˣ := ⟨2, 4, by decide, by decide⟩

def scalarCharacter : Ternary →* (ZMod 7)ˣ :=
  ZModPowerHom.hom 3 scalarTwo (by decide +kernel)

def singerPower : Multiplicative (ZMod 7) →* R :=
  ZModPowerHom.hom 7 s (Subtype.ext singer_pow_seven)

theorem frobenius_cube : f ^ 3 = 1 := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro v
  revert v
  decide +kernel

def frobeniusPower : Ternary →* R := ZModPowerHom.hom 3 f frobenius_cube

theorem scalar_conjugation (c : Ternary) (x : ZMod 7) :
    singerPower (Multiplicative.ofAdd ((scalarCharacter c : ZMod 7) * x)) =
      frobeniusPower c * singerPower (Multiplicative.ofAdd x) * (frobeniusPower c)⁻¹ := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro v
  revert c x v
  decide +kernel

variable (twisted : Bool)

abbrev alpha := TernarySwapUpperNormalGenerators.action twisted
abbrev Upper := TernarySwapUpperNormalGenerators.Upper twisted
abbrev Model := ScalarPairSwapRepresentation.Model 7 (alpha twisted) scalarCharacter

def intoWreath : Model twisted →* C2Wreath.W R :=
  ScalarPairSwapWreathImage.intoWreath 7 (alpha twisted) scalarCharacter
    singerPower frobeniusPower scalar_conjugation

def Complement : Subgroup (C2Wreath.W R) := (intoWreath twisted).range

theorem normal_generating_pairs :
    ∀ N : Subgroup (Complement twisted), N.Normal →
      ∃ x : Fin 2 → Complement twisted, Subgroup.normalClosure (Set.range x) = N :=
  ScalarPairSwapWreathImage.normal_generating_tuples 7 (alpha twisted) scalarCharacter
    singerPower frobeniusPower scalar_conjugation
    (TernarySwapUpperNormalGenerators.normal_generating_singletons twisted)

def ternaryPair : C2Wreath.W R :=
  C2WreathTwistedDiagonal.intoWreath (alpha twisted) frobeniusPower
    (inl (Multiplicative.ofAdd 1))

def generators : Fin 4 → C2Wreath.W R :=
  ![C2Wreath.firstFactor s, inl (1, s), ternaryPair twisted, inr C2Wreath.gen]

theorem firstSinger_mem : C2Wreath.firstFactor s ∈ Complement twisted := by
  refine ⟨inl (Multiplicative.ofAdd (![1, 0] : Plane)), ?_⟩
  change ScalarPairSwapWreathImage.intoWreath 7 (alpha twisted) scalarCharacter
    singerPower frobeniusPower scalar_conjugation _ = _
  rw [ScalarPairSwapWreathImage.intoWreath, SemidirectProduct.lift_inl]
  apply SemidirectProduct.ext
  · apply Prod.ext
    · exact ZModPowerHom.apply_ofAdd_one 7 s _ (by decide)
    · exact singerPower.map_one
  · rfl

theorem secondSinger_mem : (inl (1, s) : C2Wreath.W R) ∈ Complement twisted := by
  refine ⟨inl (Multiplicative.ofAdd (![0, 1] : Plane)), ?_⟩
  change ScalarPairSwapWreathImage.intoWreath 7 (alpha twisted) scalarCharacter
    singerPower frobeniusPower scalar_conjugation _ = _
  rw [ScalarPairSwapWreathImage.intoWreath, SemidirectProduct.lift_inl]
  apply SemidirectProduct.ext
  · apply Prod.ext
    · exact singerPower.map_one
    · exact ZModPowerHom.apply_ofAdd_one 7 s _ (by decide)
  · rfl

theorem ternaryPair_mem : ternaryPair twisted ∈ Complement twisted := by
  refine ⟨inr (inl (Multiplicative.ofAdd 1)), ?_⟩
  change ScalarPairSwapWreathImage.intoWreath 7 (alpha twisted) scalarCharacter
    singerPower frobeniusPower scalar_conjugation _ = _
  rw [ScalarPairSwapWreathImage.intoWreath, SemidirectProduct.lift_inr]
  rfl

theorem pure_swap_mem : (inr C2Wreath.gen : C2Wreath.W R) ∈ Complement twisted := by
  refine ⟨inr (inr C2Wreath.gen), ?_⟩
  change ScalarPairSwapWreathImage.intoWreath 7 (alpha twisted) scalarCharacter
    singerPower frobeniusPower scalar_conjugation _ = _
  rw [ScalarPairSwapWreathImage.intoWreath, SemidirectProduct.lift_inr]
  exact C2WreathTwistedDiagonal.intoWreath_inr (alpha twisted) frobeniusPower C2Wreath.gen

theorem generators_mem (i : Fin 4) : generators twisted i ∈ Complement twisted := by
  fin_cases i
  · exact firstSinger_mem twisted
  · exact secondSinger_mem twisted
  · exact ternaryPair_mem twisted
  · exact pure_swap_mem twisted

end PrimitiveAffineDegreeTwoSingerPairComplements
end SymmetricSubgroupAsymptotics

end
