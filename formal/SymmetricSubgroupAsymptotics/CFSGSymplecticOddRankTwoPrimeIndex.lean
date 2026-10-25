import SymmetricSubgroupAsymptotics.CFSGHeisenbergSLTwoTransitiveActionIndex
import SymmetricSubgroupAsymptotics.CFSGSymplecticOddRankTwoIndex

/-! The actual rank-two Heisenberg tail has index at least p*q^2
over every odd finite field, rather than only over prime fields. The
literal long central root moves the SAME original proper coset action. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGSymplecticOddRankTwoPrimeIndex
open CFSGHeisenbergCoordinateGroup CFSGHeisenbergSLTwoStabilizers
open CFSGSymplecticSerreMatrices CFSGSymplecticHeisenbergEmbedding
open CFSGSymplecticHeisenbergExtension CFSGTypeASLTwoWeyl

theorem projective_prime_mul_field_square_le_proper_index
    (K : Type) [Field K] [Finite K] (p : ℕ) [Fact p.Prime] [CharP K p]
    (hTwo : (2 : K) ≠ 0) [IsSimpleGroup (elementaryProjective K 2)]
    (H : Subgroup (elementaryProjective K 2)) (hH : H ≠ ⊤) :
    p*Nat.card K^2 ≤ H.index := by
  letI : Fintype K := Fintype.ofFinite K
  have hcentral : projectiveExtensionHom K hTwo
      (SemidirectProduct.inl (central (m := 1) (Multiplicative.ofAdd (1 : K)))) ≠ 1 := by
    intro he
    rw [projectiveExtensionHom_inl] at he
    have he' : projectiveHom K (central (m := 1) (Multiplicative.ofAdd (1 : K)))=
        projectiveHom K (central (m := 1) (1 : Multiplicative K)) := by
      simpa only [map_one] using he
    have hz : (Multiplicative.ofAdd (1 : K) : Multiplicative K)=1 :=
      projective_central_injective K hTwo he'
    exact one_ne_zero (congrArg Multiplicative.toAdd hz)
  obtain ⟨x,hx⟩ := CFSGConjugateSubgroupDegree.exists_moved_coset_of_ne_one H hH _ hcentral
  letI : MulAction (Element K 1 ⋊[tailAction K hTwo] SL2 (F := K))
      (elementaryProjective K 2 ⧸ H) := MulAction.compHom _ (projectiveExtensionHom K hTwo)
  have hb := CFSGHeisenbergSLTwoTransitiveActionIndex.degree_le_of_central_motion p
    (tailAction K hTwo) (CFSGSymplecticOddRankTwoIndex.coordinate_action K hTwo)
    x (Multiplicative.ofAdd (1 : K)) hx
  simpa only [Subgroup.index_eq_card] using hb

end SymmetricSubgroupAsymptotics.CFSGSymplecticOddRankTwoPrimeIndex

namespace SymmetricSubgroupAsymptotics.CFSGReduction
open CFSGSymplecticSerreMatrices

theorem typeC_rankTwo_prime_mul_field_square_le_proper_index (q : CFSG.PrimePower)
    (hodd : q.prime ≠ 2) [IsSimpleGroup (CFSG.Models.C 2 q)]
    (H : Subgroup (CFSG.Models.C 2 q)) (hH : H ≠ ⊤) : q.prime*q.order^2 ≤ H.index := by
  letI : Fact q.prime.Prime := ⟨q.prime_isPrime⟩
  have hTwo : (2 : q.Field) ≠ 0 :=
    CharP.cast_ne_zero_of_ne_of_prime (R := q.Field) (p := q.prime) Nat.prime_two hodd
  let e : CFSG.Models.C 2 q ≃* elementaryProjective q.Field 2 :=
    serreProjectiveEquivElementaryProjective q.Field 1
  letI : IsSimpleGroup (elementaryProjective q.Field 2) := e.symm.isSimpleGroup
  have hmap : H.map e.toMonoidHom ≠ ⊤ := by
    intro ht
    apply hH
    apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
    exact ht.trans (Subgroup.map_top_of_surjective e.toMonoidHom e.surjective).symm
  have hi := CFSGSymplecticOddRankTwoPrimeIndex.projective_prime_mul_field_square_le_proper_index
    q.Field q.prime hTwo (H.map e.toMonoidHom) hmap
  have hidx : (H.map e.toMonoidHom).index=H.index := H.index_map_equiv e
  simpa only [q.card_field,hidx] using hi

end SymmetricSubgroupAsymptotics.CFSGReduction
