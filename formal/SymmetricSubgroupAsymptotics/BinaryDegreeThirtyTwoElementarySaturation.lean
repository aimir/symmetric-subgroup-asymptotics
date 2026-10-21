import SymmetricSubgroupAsymptotics.BinaryDegreeThirtyTwoNonelementarySaturation
import SymmetricSubgroupAsymptotics.ElementaryBinaryTransitiveNormalRank
import SymmetricSubgroupAsymptotics.PermutationBinaryHead

/-! The elementary-top rank-nine alternative retains the actual
intersection head six and actual index-two image head three, together
with exact head additivity and the original mixed-radical obstruction. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical commutatorElement
namespace SymmetricSubgroupAsymptotics.BinaryPairFrame
local instance elementarySaturationFactPrimeTwo : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
variable {X : Type} [Finite X] {U : Subgroup (Equiv.Perm X)}
    (F : BinaryPairFrame U (Fin 16))

theorem elementary_proper_normal_nine_saturation
    [MulAction.IsPretransitive U X] (hU : IsPGroup 2 U)
    (hgen : MarkedC4.genRank U ≤ 9)
    (hel : BinarySquareActionStructure.SquaresActTrivially (G := F.top.range) (X := Fin 16))
    (N : Subgroup U) [N.Normal] (hproper : N ≠ ⊤) (hN : 9 ≤ MarkedC4.normalGen N) :
    N.map F.top.rangeRestrict ≠ ⊤ ∧
    MarkedC4.normalGen (N ⊓ F.top.ker) = 6 ∧
    MarkedC4.normalGen (N.map F.top.rangeRestrict) = 3 ∧
    (N.map F.top.rangeRestrict).index = 2 ∧
    (Module.finrank (ZMod 2) (primeRelativeCharacters 2 N) =
      Module.finrank (ZMod 2) (primeRelativeCharacters 2 (N ⊓ F.top.ker)) +
        Module.finrank (ZMod 2)
          (primeRelativeCharacters 2 (normalChainQuotient (N ⊓ F.top.ker) N))) ∧
    ⁅F.top.ker, N⁆ ≤ primeRelativeRadical 2 (N ⊓ F.top.ker) := by
  let f := F.top.rangeRestrict
  have hf : Function.Surjective f := F.top.rangeRestrict_surjective
  have hk : f.ker = F.top.ker := MonoidHom.ker_rangeRestrict F.top
  letI : (N.map f).Normal := Subgroup.Normal.map inferInstance f hf
  letI : MulAction.IsPretransitive F.top.range (Fin 16) := F.top_pretransitive
  have hDproper : N.map f ≠ ⊤ := by
    intro hfull
    have hs := F.normalGen_add_one_le_top_of_full_actual_image hU N hfull hproper
    have ht := MarkedC4.ActualExcessOneQuotientRank.normalGen_top_le_genRank U
    omega
  have hTopCard : Nat.card F.top.range = 16 := by
    simpa only [Nat.card_fin] using ElementaryBinaryTransitiveNormalRank.card_eq_degree hel (0 : Fin 16)
  have hcard := (N.map f).card_mul_index
  rw [hTopCard] at hcard
  have hindexge : 2 ≤ (N.map f).index := (N.map f).one_lt_index_of_ne_top hDproper
  have hDcard : Nat.card (N.map f) ≤ 8 := by nlinarith
  have hpow := MarkedC4.ActualNormalGeneratorDensity.two_pow_normalGen_le_card (N.map f)
  have hD : MarkedC4.normalGen (N.map f) ≤ 3 :=
    (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp
      (hpow.trans (hDcard.trans_eq (by decide : 8 = 2 ^ 3)))
  letI : MulAction U (Fin 16) := {
    smul := fun u i => F.top u i
    one_smul := by intro i; change F.top 1 i = i; rw [map_one]; rfl
    mul_smul := by
      intro u v i
      change F.top (u * v) i = F.top u (F.top v i)
      rw [map_mul]
      rfl }
  have hact : ∀ (u : U) (i : Fin 16), u • i = F.top u i := fun _ _ => rfl
  letI : MulAction.IsPretransitive U (Fin 16) := ⟨fun i j => by
    obtain ⟨t, ht⟩ := MulAction.exists_smul_eq F.top.range i j
    obtain ⟨u, rfl⟩ := hf t
    exact ⟨u, ht⟩⟩
  have hu : UniformSubrepresentationGeneratorBound
      (permutationFunctionRepresentation (ZMod 2) U (Fin 16)) 6 := by
    apply pGroup_uniformSubrepresentationGeneratorBound_of_head_le hU
    intro M
    exact twoGroup_permutationSubrepresentationHead_le_width hU 4
      (by norm_num only [Nat.card_fin]) (0 : Fin 16) M
  have hB := F.normalGen_le_of_uniform_pair_module hact 6 hu (N ⊓ F.top.ker) inf_le_right
  have hB' : MarkedC4.normalGen (N ⊓ f.ker) ≤ 6 := by rw [hk]; exact hB
  obtain ⟨heq, hBexact, hDexact⟩ := pGroup_actual_intersection_head_additivity_of_saturation
    2 f hf N hU 6 3 hN hB' hD
  have htransport (K : Subgroup U) [K.Normal] (he : f.ker = K) :
      Module.finrank (ZMod 2) (primeRelativeCharacters 2 N) =
        Module.finrank (ZMod 2) (primeRelativeCharacters 2 (N ⊓ K)) +
          Module.finrank (ZMod 2) (primeRelativeCharacters 2 (normalChainQuotient (N ⊓ K) N)) := by
    subst K
    exact heq
  have heq' := htransport F.top.ker hk
  rw [hDexact] at hpow
  norm_num only [Nat.reducePow] at hpow
  have hindex : (N.map f).index = 2 := by nlinarith
  rw [hk] at hBexact
  refine ⟨hDproper, hBexact, hDexact, hindex, heq', ?_⟩
  exact mixed_commutator_le_intersection_radical_of_head_additivity
    2 (N ⊓ F.top.ker) N inf_le_left F.top.ker rfl heq'

end SymmetricSubgroupAsymptotics.BinaryPairFrame
