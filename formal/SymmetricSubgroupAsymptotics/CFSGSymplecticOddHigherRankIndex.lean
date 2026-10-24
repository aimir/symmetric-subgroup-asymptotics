import SymmetricSubgroupAsymptotics.CFSGSymplecticHeisenbergUniformActionIndex
import SymmetricSubgroupAsymptotics.CFSGSymplecticProjectiveRealization
import SymmetricSubgroupAsymptotics.CFSGSimpleIndexTransport

/-! Every actual proper subgroup of the SAME original odd-characteristic
C_r model, r>=3, has index at least p*q^(2r-2). Actual long-centre
injection and inherited original simplicity produce a moved proper
coset. The actual Heisenberg semidirect action then gives the bound.
No subgroup classification, K-linearity, or parabolic callback occurs. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGSymplecticOddHigherRankIndex

open CFSGHeisenbergCoordinateGroup CFSGSymplecticSerreMatrices
open CFSGSymplecticHeisenbergUniformEmbedding CFSGSymplecticHeisenbergUniformExtension
variable (K : Type) [Field K]

theorem projective_prime_mul_field_power_le_proper_index [Finite K]
    (m : ℕ) (hm : 2 ≤ m) (hTwo : (2 : K) ≠ 0)
    (p : ℕ) [Fact p.Prime] [CharP K p]
    [IsSimpleGroup (elementaryProjective K (m + 1))]
    (H : Subgroup (elementaryProjective K (m + 1))) (hH : H ≠ ⊤) :
    p * Nat.card K ^ (2 * m) ≤ H.index := by
  have hcentral : projectiveExtensionHom K m (by omega) hTwo
      (SemidirectProduct.inl (central (m := m) (Multiplicative.ofAdd (1 : K)))) ≠ 1 := by
    intro he
    rw [projectiveExtensionHom_inl] at he
    have he' : projectiveHom K m (by omega) (central (m := m) (Multiplicative.ofAdd (1 : K))) =
        projectiveHom K m (by omega) (central (m := m) (1 : Multiplicative K)) := by
      simpa only [map_one] using he
    have hz : (Multiplicative.ofAdd (1 : K) : Multiplicative K) = 1 :=
      projective_central_injective K m (by omega) hTwo he'
    exact one_ne_zero (congrArg Multiplicative.toAdd hz)
  obtain ⟨x, hx⟩ := CFSGConjugateSubgroupDegree.exists_moved_coset_of_ne_one H hH _ hcentral
  letI : MulAction
      (Element K m ⋊[tailAction K m (by omega) hTwo] elementaryRootGroup K m)
      (elementaryProjective K (m + 1) ⧸ H) :=
    MulAction.compHom _ (projectiveExtensionHom K m (by omega) hTwo)
  have hb := CFSGSymplecticHeisenbergUniformActionIndex.degree_le_of_central_motion
    K m hm hTwo p x (Multiplicative.ofAdd (1 : K)) hx
  simpa only [Subgroup.index_eq_card] using hb

end SymmetricSubgroupAsymptotics.CFSGSymplecticOddHigherRankIndex

namespace SymmetricSubgroupAsymptotics.CFSGReduction

open CFSGSymplecticSerreMatrices PrimitiveSocleRawStructure

theorem typeC_odd_prime_mul_field_power_le_proper_index (r : ℕ) (hr : 3 ≤ r)
    (q : CFSG.PrimePower) (hTwo : (2 : q.Field) ≠ 0)
    [IsSimpleGroup (CFSG.Models.C r q)]
    (H : Subgroup (CFSG.Models.C r q)) (hH : H ≠ ⊤) :
    q.prime * q.order ^ (2 * r - 2) ≤ H.index := by
  obtain ⟨m, rfl⟩ : ∃ m : ℕ, r = m + 1 := ⟨r - 1, by omega⟩
  have hexp : 2 * (m + 1) - 2 = 2 * m := by omega
  rw [hexp]
  letI : Fact q.prime.Prime := ⟨q.prime_isPrime⟩
  let e : CFSG.Models.C (m + 1) q ≃* elementaryProjective q.Field (m + 1) :=
    serreProjectiveEquivElementaryProjective q.Field m
  letI : IsSimpleGroup (elementaryProjective q.Field (m + 1)) := e.symm.isSimpleGroup
  have hmap : H.map e.toMonoidHom ≠ ⊤ := by
    intro ht
    apply hH
    apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
    exact ht.trans (Subgroup.map_top_of_surjective e.toMonoidHom e.surjective).symm
  have hb := CFSGSymplecticOddHigherRankIndex.projective_prime_mul_field_power_le_proper_index
    q.Field m (by omega) hTwo q.prime (H.map e.toMonoidHom) hmap
  have hi : (H.map e.toMonoidHom).index = H.index := H.index_map_equiv e
  simpa only [q.card_field, hi] using hb

theorem typeC_odd_prime_mul_field_power_le_leastProperIndex (r : ℕ) (hr : 3 ≤ r)
    (q : CFSG.PrimePower) (hTwo : (2 : q.Field) ≠ 0)
    [IsSimpleGroup (CFSG.Models.C r q)] (ell : ℕ)
    (hell : LeastProperIndex (CFSG.Models.C r q) ell) :
    q.prime * q.order ^ (2 * r - 2) ≤ ell := by
  obtain ⟨H, hH, he⟩ := hell.1
  exact (typeC_odd_prime_mul_field_power_le_proper_index r hr q hTwo H hH).trans_eq he

end SymmetricSubgroupAsymptotics.CFSGReduction
