import SymmetricSubgroupAsymptotics.BinarySylowAutomorphismTransitiveAction
import SymmetricSubgroupAsymptotics.RegularFourByTwoSeedCoordinates
import SymmetricSubgroupAsymptotics.BinaryEightSeed2Transitivity
import SymmetricSubgroupAsymptotics.S8AboveEightBinarySeedCanonicalCoverage
import Mathlib.Tactic.NormNum

/-! The original regularC4×C2 seed needs no finite adjunction forest.
Burnside transfer and its actual binary automorphism group rule out this Sylow2 in a nonbinary degree8 source;
the actual larger Sylow subgroup retains its original point action. -/
set_option autoImplicit false
noncomputable section
open scoped Pointwise
namespace SymmetricSubgroupAsymptotics.S8Seed2CanonicalCoverage
abbrev Ambient := Equiv.Perm (Fin 8)
abbrev H : Subgroup Ambient := Subgroup.closure (Set.range BinaryMenuCayley8T2.generators)

theorem complete (U : Subgroup Ambient) (hHU : H ≤ U) (hnot : ¬IsPGroup 2 U) :
    ∃ i : Fin 24,∃ c : Ambient,MulAut.conj c • U =
      Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeEightCanonicalCatalogue.canonical i := by
  letI : MulAction.IsPretransitive U (Fin 8) := ⟨by
    intro x y
    obtain ⟨g,hg,hxy⟩ := BinaryEightSeed2Transitivity.transitive x y
    exact ⟨⟨g,hHU hg⟩,hxy⟩⟩
  let K : Subgroup U := H.subgroupOf U
  let e : K ≃* H := Subgroup.subgroupOfEquivOfLe hHU
  let chart : FourByTwoAutomorphismBinary.Model ≃* K :=
    RegularFourByTwoSeedCoordinates.chart.trans e.symm
  have hkAut : IsPGroup 2 (MulAut K) :=
    FourByTwoAutomorphismBinary.automorphisms_isPGroup.of_equiv (MulAut.congr chart)
  have hkcomm : IsMulCommutative K := by
    refine ⟨⟨?_⟩⟩
    intro u v
    obtain ⟨a,rfl⟩ := chart.surjective u
    obtain ⟨b,rfl⟩ := chart.surjective v
    rw [←map_mul,←map_mul,mul_comm]
  have hkcard : Nat.card K = 8 :=
    (Nat.card_congr e.toEquiv).trans BinaryMenuCayley8T2.exact_card
  have hK : IsPGroup 2 K := IsPGroup.of_card (n := 3) hkcard
  obtain ⟨Q,hKQ,hcard⟩ := exists_larger_sylow_of_binary_automorphism_seed (X := Fin 8)
    K hK hkcomm hkAut 3 (by norm_num) hnot
  let P : Subgroup Ambient := (Q : Subgroup U).map U.subtype
  have hPU : P ≤ U := by
    rintro g ⟨u,_,rfl⟩
    exact u.property
  have hHP : H ≤ P := by
    intro g hg
    exact ⟨⟨g,hHU hg⟩,hKQ hg,rfl⟩
  have h8 : 8 < Nat.card P := by
    have he := Nat.card_congr
      ((Q : Subgroup U).equivMapOfInjective U.subtype Subtype.val_injective).toEquiv
    exact hkcard.symm.trans_lt (hcard.trans_eq he)
  exact S8AboveEightBinarySeedCanonicalCoverage.complete U P hPU
    (Q.isPGroup'.map U.subtype)
    (permutationSubgroupTransitive_mono H P hHP BinaryEightSeed2Transitivity.transitive) h8 hnot

theorem complete_of_conjugate (U Q : Subgroup Ambient) (hQU : Q ≤ U)
    (c : Ambient) (hc : MulAut.conj c • Q = H) (hnot : ¬IsPGroup 2 U) :
    ∃ i : Fin 24,∃ d : Ambient,MulAut.conj d • U =
      Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeEightCanonicalCatalogue.canonical i := by
  have hHU : H ≤ MulAut.conj c • U := by
    rw [←hc]
    change Q.map (MulAut.conj c).toMonoidHom ≤ U.map (MulAut.conj c).toMonoidHom
    exact Subgroup.map_mono hQU
  have hnot' : ¬IsPGroup 2 ↥(MulAut.conj c • U) := fun hp =>
    hnot (S8CanonicalNonbinaryTransport.isPGroup_of_conjugate U _ c rfl hp)
  obtain ⟨i,d,hd⟩ := complete (MulAut.conj c • U) hHU hnot'
  refine ⟨i,d*c,?_⟩
  rw [map_mul,mul_smul]
  exact hd

end SymmetricSubgroupAsymptotics.S8Seed2CanonicalCoverage
end
