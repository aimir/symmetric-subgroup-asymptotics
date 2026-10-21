import SymmetricSubgroupAsymptotics.CyclicSylowTwoLargerSeed
import SymmetricSubgroupAsymptotics.BinaryEightSeed1Transitivity
import SymmetricSubgroupAsymptotics.S8AboveEightBinarySeedCanonicalCoverage
import Mathlib.Tactic.NormNum

/-! The original cyclic regular seed needs no finite adjunction forest.
Burnside transfer rules out a cyclic Sylow2 in a nonbinary degree8 source;
the actual larger Sylow subgroup retains its original point action. -/
set_option autoImplicit false
noncomputable section
open scoped Pointwise
namespace SymmetricSubgroupAsymptotics.S8Seed1CanonicalCoverage
abbrev Ambient := Equiv.Perm (Fin 8)
abbrev H : Subgroup Ambient := Subgroup.closure (Set.range BinaryMenuCayley8T1.generators)

theorem seed_cyclic : IsCyclic H := by
  apply (H.isCyclic_iff_exists_zpowers_eq_top).mpr
  refine ⟨BinaryMenuCayley8T1.generators 0,?_⟩
  have hr : Set.range BinaryMenuCayley8T1.generators = {BinaryMenuCayley8T1.generators 0} := by
    ext g
    constructor
    · rintro ⟨i,rfl⟩
      have hi : i = 0 := Subsingleton.elim _ _
      simp only [hi,Set.mem_singleton_iff]
    · intro hg
      exact ⟨0,(Set.mem_singleton_iff.mp hg).symm⟩
  change Subgroup.zpowers _ = Subgroup.closure _
  rw [hr,Subgroup.zpowers_eq_closure]

theorem complete (U : Subgroup Ambient) (hHU : H ≤ U) (hnot : ¬IsPGroup 2 U) :
    ∃ i : Fin 24,∃ c : Ambient,MulAut.conj c • U =
      Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeEightCanonicalCatalogue.canonical i := by
  letI : MulAction.IsPretransitive U (Fin 8) := ⟨by
    intro x y
    obtain ⟨g,hg,hxy⟩ := BinaryEightSeed1Transitivity.transitive x y
    exact ⟨⟨g,hHU hg⟩,hxy⟩⟩
  let K : Subgroup U := H.subgroupOf U
  let e : K ≃* H := Subgroup.subgroupOfEquivOfLe hHU
  letI : IsCyclic H := seed_cyclic
  have hkcyclic : IsCyclic K := isCyclic_of_surjective e.symm e.symm.surjective
  have hkcard : Nat.card K = 8 :=
    (Nat.card_congr e.toEquiv).trans BinaryMenuCayley8T1.exact_card
  have hK : IsPGroup 2 K := IsPGroup.of_card (n := 3) hkcard
  have hdvd : 8 ∣ Nat.card U := by
    have h := K.card_subgroup_dvd_card
    rwa [hkcard] at h
  have hmin : (Nat.card U).minFac = 2 :=
    (Nat.minFac_eq_two_iff _).mpr ((by decide : 2 ∣ 8).trans hdvd)
  obtain ⟨Q,hKQ,hcard⟩ := exists_larger_sylow_of_cyclic_binary_seed (X := Fin 8)
    K hK hkcyclic hmin 3 (by norm_num) hnot
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
    (permutationSubgroupTransitive_mono H P hHP BinaryEightSeed1Transitivity.transitive) h8 hnot

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

end SymmetricSubgroupAsymptotics.S8Seed1CanonicalCoverage
end
