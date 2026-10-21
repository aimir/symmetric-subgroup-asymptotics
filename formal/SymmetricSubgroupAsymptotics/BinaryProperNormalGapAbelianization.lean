import SymmetricSubgroupAsymptotics.FiniteAbelianSquareKernelQuotient
import SymmetricSubgroupAsymptotics.PGroupGeneratorAbelianizationOrder
import SymmetricSubgroupAsymptotics.PGroupNormalGeneratorCharacterEquality
import SymmetricSubgroupAsymptotics.PrimeRelativeRadicalPresentation

/-! A strict gap for every proper original normal subgroup forces the
full original abelianization to be elementary. The subgroup used in the
proof is the literal preimage of the square-kernel in that abelianization;
no elementary-abelianization assumption or quotient rank replacement is
made in constructing it. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped commutatorElement
namespace SymmetricSubgroupAsymptotics
local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

/-- In an abelian ambient 2-group, a subgroup of exponent two has order
exactly two to its ambient normal generator number. -/
theorem binary_abelian_subgroup_card_eq_pow_normalGen
    {A : Type} [CommGroup A] [Finite A] (hA : IsPGroup 2 A)
    (T : Subgroup A) (hT : ∀ t : T, (t : A)^2=1) :
    Nat.card T = 2 ^ MarkedC4.normalGen T := by
  have hR : primeRelativeRadical 2 T = ⊥ := by
    rw [primeRelativeRadical_eq_powerCommutator,primeRelativePowerCommutator]
    apply le_antisymm ?_ bot_le
    apply sup_le
    · apply (Subgroup.closure_le (⊥ : Subgroup A)).mpr
      rintro x ⟨t,rfl⟩
      change (t : A)^2 ∈ (⊥ : Subgroup A)
      rw [hT t]
      exact Subgroup.one_mem _
    · apply Subgroup.commutator_le.mpr
      intro a _ b _
      simp [commutatorElement_def,mul_assoc]
  have hc := primeRelativeRadical_card_factorization 2 T
  rw [← pGroup_normalGen_eq_primeRelativeHead 2 hA,hR] at hc
  simpa only [Subgroup.card_bot,mul_one] using hc

/-- The square-kernel of the full abelianization has at least the
original ordinary generator rank, measured by its ambient normal rank. -/
theorem binary_abelianization_square_kernel_normalGen_ge
    {G : Type} [Group G] [Finite G] (hG : IsPGroup 2 G) :
    MarkedC4.genRank G ≤ MarkedC4.normalGen
      (powMonoidHom (α := Abelianization G) 2).ker := by
  let A := Abelianization G
  let T : Subgroup A := (powMonoidHom (α := A) 2).ker
  let V := Multiplicative (PrimeAbelianization 2 G)
  let f : A →* V := Abelianization.lift (primeAbelianizationGroupMap 2 G)
  have hf : Function.Surjective f := by
    intro x
    obtain ⟨g,hg⟩ := primeAbelianizationGroupMap_surjective 2 G x
    exact ⟨Abelianization.of g,(Abelianization.lift_apply_of _ _).trans hg⟩
  have hV : (powMonoidHom (α := V) 2).ker=⊤ := by
    apply top_unique
    intro v _
    change v^2=1
    apply Multiplicative.toAdd.injective
    rw [toAdd_pow]
    exact ZModModule.char_nsmul_eq_zero 2 _
  have hc := FiniteAbelianSquareKernelQuotient.card_square_kernel_le f hf
  rw [hV,Subgroup.card_top] at hc
  have hcardV : Nat.card V = 2 ^ Module.finrank (ZMod 2) (PrimeCharacters 2 G) := by
    rw [Nat.card_congr (Multiplicative.toAdd : V ≃ PrimeAbelianization 2 G)]
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod,
      Subspace.dual_finrank_eq]
  have hA : IsPGroup 2 A := hG.of_surjective Abelianization.of
    (QuotientGroup.mk'_surjective (commutator G))
  have hcardT : Nat.card T = 2 ^ MarkedC4.normalGen T :=
    binary_abelian_subgroup_card_eq_pow_normalGen hA T (fun t => t.property)
  rw [hcardV,hcardT] at hc
  exact (pGroup_genRank_le_primeCharacterRank 2 hG).trans
    ((Nat.pow_le_pow_iff_right (by decide : 1<2)).mp hc)

/-- A rank-maximal proper normal cannot coexist with a strict proper
normal rank gap. The contradiction uses its actual abelianization image. -/
theorem binary_abelianization_exponent_of_strict_proper_normal_gap
    {G : Type} [Group G] [Finite G] (hG : IsPGroup 2 G)
    (hgap : ∀ (N : Subgroup G), N.Normal → N≠⊤ →
      MarkedC4.normalGen N < MarkedC4.genRank G) :
    ∀ a : Abelianization G, a^2=1 := by
  let q : G →* Abelianization G := Abelianization.of
  have hq : Function.Surjective q := QuotientGroup.mk'_surjective (commutator G)
  let T : Subgroup (Abelianization G) := (powMonoidHom (α := Abelianization G) 2).ker
  let N : Subgroup G := T.comap q
  have hmap : N.map q=T := Subgroup.map_comap_eq_self_of_surjective hq T
  have hlarge : MarkedC4.genRank G ≤ MarkedC4.normalGen N := by
    have hm := MarkedC4.normalGen_map_le q hq N
    rw [hmap] at hm
    exact (binary_abelianization_square_kernel_normalGen_ge hG).trans hm
  have hN : N=⊤ := by
    by_contra hn
    exact (not_lt_of_ge hlarge) (hgap N inferInstance hn)
  intro a
  obtain ⟨g,rfl⟩ := hq a
  have hg : g∈N := by rw [hN]; exact Subgroup.mem_top g
  exact hg

end SymmetricSubgroupAsymptotics
