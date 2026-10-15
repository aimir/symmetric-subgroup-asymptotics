import SymmetricSubgroupAsymptotics.CentralPrimeFactorQuotientSocles
import SymmetricSubgroupAsymptotics.CyclicImageNormalAxisGenerators
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoCentralProductModels
import SymmetricSubgroupAsymptotics.NaturalFourNormalChains
import SymmetricSubgroupAsymptotics.DihedralNormalGenerators
import SymmetricSubgroupAsymptotics.DirectProductNormalGenerators

/-! The exact central ternary products needed by full four-block modules.
S3 × C3 has cyclic image C2 × C3 and a noncentral rotation core. S4 × C3
then uses its actual Klein kernel and actual pairing map. Thus its bound is
one, although the two factors have separate one-generator bounds. -/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.TernaryCentralComplementSocles

open DihedralGroup
open Non2UnipotentPrefixFiniteMenu.CentralBinaryProductModels

abbrev C3 := Multiplicative (ZMod 3)
abbrev C2 := Multiplicative (ZMod 2)
abbrev D3 := DihedralGroup 3

instance ternary_simple : IsSimpleGroup C3 :=
  isSimpleGroup_of_prime_card (p := 3) (by simp [C3,Nat.card_eq_fintype_card])

def rotationCore : CentralBinaryProductCore D3 where
  V := (DihedralNormalGenerators.parity 3).ker
  minimal := by
    intro W hW hWV
    by_cases hb : W = ⊥
    · exact Or.inl hb
    right
    obtain ⟨x,hx,hxne⟩ := W.bot_or_exists_ne_one.resolve_left hb
    have hrot := OddPrimeDihedralNormalChain.rotation_mem_of_ne_one
      (by decide : 2 < 3) W hW x hx hxne
    apply le_antisymm hWV
    rw [DihedralNormalGenerators.parity_ker]
    exact Subgroup.zpowers_le.mpr hrot
  selfCentralizing := by
    intro x hx
    have hrot : r (1 : ZMod 3) ∈ (DihedralNormalGenerators.parity 3).ker := rfl
    have hc := hx (r 1) hrot
    cases x with
    | r i => rfl
    | sr i =>
      exact ((show ∀ i : ZMod 3, (sr i : D3)*r 1 ≠ r 1*sr i by decide +kernel) i hc).elim
  noFixed := by
    intro v hv hc
    cases v with
    | r i =>
      exact (show ∀ i : ZMod 3, (sr 0 : D3)*r i = r i*sr 0 → r i = 1 by
        decide +kernel) i (hc (sr 0))
    | sr i =>
      have hn : (sr i : D3) ∉ (DihedralNormalGenerators.parity 3).ker := by
        change Multiplicative.ofAdd (1 : ZMod 2) ≠ 1
        decide +kernel
      exact (hn hv).elim

theorem rotationCore_ne_bot : rotationCore.V ≠ ⊥ := by
  intro h
  have hm : r (1 : ZMod 3) ∈ rotationCore.V := rfl
  rw [h] at hm
  exact (by decide : (r (1 : ZMod 3) : D3) ≠ 1) (Subgroup.mem_bot.mp hm)

instance binary_ternary_cyclic : IsCyclic (C2 × C3) :=
  Group.isCyclic_prod_iff.mpr ⟨inferInstance,inferInstance,by
    norm_num [C2,C3,Nat.card_eq_fintype_card]⟩

instance rotation_axis_cyclic : IsCyclic (rotationCore.productCentral C3) := by
  apply isCyclic_of_injective
    ((MonoidHom.snd D3 C3).comp (rotationCore.productCentral C3).subtype)
  intro x y h
  apply Subtype.ext
  apply Prod.ext
  · exact ((rotationCore.mem_productCentral C3 x.1).mp x.2).trans
      ((rotationCore.mem_productCentral C3 y.1).mp y.2).symm
  · exact h

def parityProduct : D3 × C3 →* C2 × C3 :=
  (DihedralNormalGenerators.parity 3).prodMap (MonoidHom.id C3)

theorem parityProduct_surjective : Function.Surjective parityProduct := by
  intro q
  have hq : q.1 = 1 ∨ q.1 = Multiplicative.ofAdd 1 :=
    (show ∀ z : C2, z = 1 ∨ z = Multiplicative.ofAdd 1 by decide +kernel) q.1
  rcases hq with h | h
  · exact ⟨(r 0,q.2),Prod.ext h.symm rfl⟩
  · exact ⟨(sr 0,q.2),Prod.ext h.symm rfl⟩

theorem parityProduct_ker : parityProduct.ker = rotationCore.productCore C3 := by
  ext x
  change (DihedralNormalGenerators.parity 3 x.1,x.2) = 1 ↔
    DihedralNormalGenerators.parity 3 x.1 = 1 ∧ x.2 = 1
  exact Prod.ext_iff

theorem dihedral_product_normal_singletons :
    ∀ N : Subgroup (D3 × C3), N.Normal →
      ∃ x : Fin 1 → D3 × C3, Subgroup.normalClosure (Set.range x) = N := by
  apply normal_generating_singletons_of_cyclic_image_axis parityProduct parityProduct_surjective
    (rotationCore.productCentral C3)
  · intro h
    have hm : (r (1 : ZMod 3),(1 : C3)) ∈ parityProduct.ker := rfl
    have he := (rotationCore.mem_productCentral C3 _).mp (h hm)
    exact (by decide : (r (1 : ZMod 3) : D3) ≠ 1) he
  · intro N hN
    rw [parityProduct_ker]
    exact rotationCore.normal_contains_productCore_or_le_productCentral C3 N hN

theorem symmetricThree_product_socle_of_surjective {X : Type} [Group X]
    (rho : Equiv.Perm (Fin 3) × C3 →* X) (hrho : Function.Surjective rho) :
    SocleNormalGeneratorBound X 1 := by
  let e := NaturalFourNormalChains.dihedralThree.prodMap (MonoidHom.id C3)
  have he : Function.Surjective e := by
    intro x
    obtain ⟨d,hd⟩ := NaturalFourNormalChains.dihedralThree_surjective x.1
    exact ⟨(d,x.2),Prod.ext hd rfl⟩
  let f := rho.comp e
  have hf : Function.Surjective f := hrho.comp he
  exact CyclicSocleQuotientTools.socleBound_equiv
    (QuotientGroup.quotientKerEquivOfSurjective f hf)
    (quotientSocleNormalGeneratorBound_of_normal_generating_tuples
      dihedral_product_normal_singletons f.ker)

theorem symmetricFour_product_socle_of_surjective {X : Type} [Group X]
    (rho : Equiv.Perm (Fin 4) × C3 →* X) (hrho : Function.Surjective rho) :
    SocleNormalGeneratorBound X 1 := by
  apply s4Core.product_socle_of_surjective C3 _ NaturalS4.pairing
    NaturalS4.pairing_surjective NaturalS4.ker_pairing (by decide) _ _ rho hrho
  · change NaturalS4.klein ≠ ⊥
    intro h
    have hcard := NaturalS4.card_klein
    rw [h] at hcard
    norm_num at hcard
  · intro N hN
    letI := hN
    exact socleNormalGeneratorBound_one_of_normal_total
      (normalSubgroups_total_of_surjective (QuotientGroup.mk' N)
        (QuotientGroup.mk'_surjective N) NaturalFourNormalChains.symmetric_normal_total)
  · intro N hN
    letI := hN
    exact symmetricThree_product_socle_of_surjective
      (QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N)

theorem alternatingFour_product_socle_of_surjective {X : Type} [Group X]
    (rho : alternatingGroup (Fin 4) × C3 →* X) (hrho : Function.Surjective rho) :
    SocleNormalGeneratorBound X 2 :=
  CyclicSocleQuotientTools.socleBound_equiv
    (QuotientGroup.quotientKerEquivOfSurjective rho hrho)
    (quotientSocle_of_product_normal_generators
      (normal_generating_singletons_of_finite_normal_total
        NaturalFourNormalChains.alternating_normal_total)
      normal_generating_singletons_of_isCyclic rho.ker)

end SymmetricSubgroupAsymptotics.TernaryCentralComplementSocles

end
