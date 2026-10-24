import SymmetricSubgroupAsymptotics.CFSGSymplecticOddRankTwoIndex
import SymmetricSubgroupAsymptotics.CFSGHeisenbergPrimeFieldIndex

/-! The actual original C2 model over an odd prime field has proper
index at least p cubed, using the same literal Heisenberg semidirect
embedding and stronger coupled prime-field index estimate. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGSymplecticPrimeFieldRankTwoIndex
open CFSGHeisenbergCoordinateGroup CFSGTypeASLTwoWeyl
open CFSGSymplecticSerreMatrices CFSGSymplecticHeisenbergEmbedding
open CFSGSymplecticHeisenbergExtension CFSGSymplecticOddRankTwoIndex

theorem projective_prime_cube_le_proper_index (K : Type) [Field K] [Finite K]
    (p : ℕ) [Fact p.Prime] [CharP K p] (hK : Nat.card K = p) (hTwo : (2 : K) ≠ 0)
    [IsSimpleGroup (elementaryProjective K 2)]
    (H : Subgroup (elementaryProjective K 2)) (hH : H ≠ ⊤) : p^3 ≤ H.index := by
  have hcentral : projectiveExtensionHom K hTwo
      (SemidirectProduct.inl (central (m := 1) (Multiplicative.ofAdd (1 : K)))) ≠ 1 := by
    intro he
    rw [projectiveExtensionHom_inl] at he
    have he' : projectiveHom K (central (m := 1) (Multiplicative.ofAdd (1 : K))) =
        projectiveHom K (central (m := 1) (1 : Multiplicative K)) := by
      simpa only [map_one] using he
    have hz : (Multiplicative.ofAdd (1 : K) : Multiplicative K) = 1 :=
      projective_central_injective K hTwo he'
    exact one_ne_zero (congrArg Multiplicative.toAdd hz)
  obtain ⟨x, hx⟩ := CFSGConjugateSubgroupDegree.exists_moved_coset_of_ne_one H hH _ hcentral
  letI : MulAction (Element K 1 ⋊[tailAction K hTwo] SL2 (F := K))
      (elementaryProjective K 2 ⧸ H) := MulAction.compHom _ (projectiveExtensionHom K hTwo)
  have hb := CFSGHeisenbergPrimeFieldIndex.degree_le_of_central_motion p hK
    (tailAction K hTwo) (coordinate_action K hTwo) x (Multiplicative.ofAdd (1 : K)) hx
  simpa only [Subgroup.index_eq_card] using hb

end SymmetricSubgroupAsymptotics.CFSGSymplecticPrimeFieldRankTwoIndex

namespace SymmetricSubgroupAsymptotics.CFSGReduction
open CFSGSymplecticSerreMatrices

theorem typeC_rankTwo_prime_cube_le_proper_index (q : CFSG.PrimePower)
    (hprime : q.order = q.prime) (hTwo : (2 : q.Field) ≠ 0)
    [IsSimpleGroup (CFSG.Models.C 2 q)]
    (H : Subgroup (CFSG.Models.C 2 q)) (hH : H ≠ ⊤) : q.order^3 ≤ H.index := by
  letI : Fact q.prime.Prime := ⟨q.prime_isPrime⟩
  let e : CFSG.Models.C 2 q ≃* elementaryProjective q.Field 2 :=
    serreProjectiveEquivElementaryProjective q.Field 1
  letI : IsSimpleGroup (elementaryProjective q.Field 2) := e.symm.isSimpleGroup
  have hmap : H.map e.toMonoidHom ≠ ⊤ := by
    intro ht
    apply hH
    apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
    exact ht.trans (Subgroup.map_top_of_surjective e.toMonoidHom e.surjective).symm
  have h := CFSGSymplecticPrimeFieldRankTwoIndex.projective_prime_cube_le_proper_index
    q.Field q.prime (q.card_field.trans hprime) hTwo (H.map e.toMonoidHom) hmap
  have hi : (H.map e.toMonoidHom).index = H.index := H.index_map_equiv e
  simpa only [hprime, hi] using h

end SymmetricSubgroupAsymptotics.CFSGReduction
