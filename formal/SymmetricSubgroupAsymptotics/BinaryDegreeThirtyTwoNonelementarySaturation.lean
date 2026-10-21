import SymmetricSubgroupAsymptotics.BinaryDegreeSixteenLargeProperNormalIndex
import SymmetricSubgroupAsymptotics.BinaryPairIntersectionRadicalStabilizer
import SymmetricSubgroupAsymptotics.NormalHeadActualIntersectionImage
import SymmetricSubgroupAsymptotics.BinaryTransitiveProperNormalQuarterPlusOne

/-! A hypothetical proper rank-nine normal in an original degree32
source with at most nine ordinary generators saturates the literal
intersection/image filtration. Its actual top image has index two, its
actual intersection has head four, and mixed commutators land in that
same intersection's whole-ambient radical. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical commutatorElement
namespace SymmetricSubgroupAsymptotics.BinaryPairFrame
local instance binaryDegreeThirtyTwoNonelementarySaturationFactPrimeTwo : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
variable {X : Type} [Finite X] {U : Subgroup (Equiv.Perm X)}
    (F : BinaryPairFrame U (Fin 16))

theorem nonelementary_proper_normal_nine_saturation
    [MulAction.IsPretransitive U X] (hU : IsPGroup 2 U)
    (hgen : MarkedC4.genRank U ≤ 9)
    (hnon : ¬BinarySquareActionStructure.SquaresActTrivially (G := F.top.range) (X := Fin 16))
    (N : Subgroup U) [N.Normal] (hproper : N ≠ ⊤) (hN : 9 ≤ MarkedC4.normalGen N) :
    N.map F.top.rangeRestrict ≠ ⊤ ∧
    MarkedC4.normalGen (N ⊓ F.top.ker) = 4 ∧
    MarkedC4.normalGen (N.map F.top.rangeRestrict) = 5 ∧
    6 ≤ MarkedC4.genRank F.top.range ∧
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
  have hTop := F.top_isPGroup hU
  have hDproper : N.map f ≠ ⊤ := by
    intro hfull
    have hs := F.normalGen_add_one_le_top_of_full_actual_image hU N hfull hproper
    have ht := MarkedC4.ActualExcessOneQuotientRank.normalGen_top_le_genRank U
    omega
  have hD := twoGroup_transitive_proper_normalGen_le_quarter_add_one F.top.range hTop (N.map f) hDproper
  norm_num only [Nat.card_fin] at hD
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
  have hnonU : ¬BinarySquareActionStructure.SquaresActTrivially (G := U) (X := Fin 16) := by
    intro hel
    apply hnon
    intro t i
    obtain ⟨u, rfl⟩ := hf t
    change F.top u ^ 2 • i = i
    rw [← map_pow]
    exact hel u i
  have hB := F.normalGen_le_quarter_of_not_elementary hact hU hnonU
    (N ⊓ F.top.ker) inf_le_right
  norm_num only [Nat.card_fin] at hB
  have hB' : MarkedC4.normalGen (N ⊓ f.ker) ≤ 4 := by rw [hk]; exact hB
  obtain ⟨heq, hBexact, hDexact⟩ := pGroup_actual_intersection_head_additivity_of_saturation
    2 f hf N hU 4 5 hN hB' hD
  have htransport (K : Subgroup U) [K.Normal] (he : f.ker = K) :
      Module.finrank (ZMod 2) (primeRelativeCharacters 2 N) =
        Module.finrank (ZMod 2) (primeRelativeCharacters 2 (N ⊓ K)) +
          Module.finrank (ZMod 2) (primeRelativeCharacters 2 (normalChainQuotient (N ⊓ K) N)) := by
    subst K
    exact heq
  have heq' := htransport F.top.ker hk
  have hhigh := twoGroup_degree_sixteen_six_le_genRank_of_proper_normal_five F.top.range hTop
    (by simp only [Nat.card_fin]) (N.map f) hDproper hDexact.ge
  have hindex := twoGroup_degree_sixteen_proper_normal_five_index_two F.top.range hTop
    (by simp only [Nat.card_fin]) (N.map f) hDproper hDexact.ge
  rw [hk] at hBexact
  refine ⟨hDproper, hBexact, hDexact, hhigh, hindex, heq', ?_⟩
  exact mixed_commutator_le_intersection_radical_of_head_additivity
    2 (N ⊓ F.top.ker) N inf_le_left F.top.ker rfl heq'

end SymmetricSubgroupAsymptotics.BinaryPairFrame
