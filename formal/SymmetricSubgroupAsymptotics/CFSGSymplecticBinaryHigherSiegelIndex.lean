import SymmetricSubgroupAsymptotics.CFSGSymplecticHigherSiegelStabilizerIndex
import SymmetricSubgroupAsymptotics.CFSGSymplecticProjectiveRealization
import SymmetricSubgroupAsymptotics.CFSGSimpleIndexTransport
import SymmetricSubgroupAsymptotics.CFSGConjugateSubgroupDegree

/-! The exact higher-rank binary Siegel index bound for EVERY proper
subgroup of the literal elementary projective group and the SAME
original C model. Simplicity produces a moved actual coset for one
literal nontrivial offdiagonal shear; its actual same-M index bound
then applies. The literal theorem does not assume original-C simplicity. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGSymplecticBinaryHigherSiegelIndex

open SymmetricMatrixCongruenceAction CFSGSymplecticSerreMatrices
open CFSGSymplecticHigherSiegelEmbedding CFSGSymplecticHigherSiegelExtension
open CFSGSymplecticHigherSiegelStabilizerIndex
variable (K : Type) [Field K] [Finite K] [CharP K 2]

/-- Only simplicity of the literal group itself is an input here. -/
theorem projective_two_frame_le_two_mul_proper_index (m : ℕ) (hm : 0 < m)
    [IsSimpleGroup (elementaryProjective K (m + 1))]
    (H : Subgroup (elementaryProjective K (m + 1))) (hH : H ≠ ⊤) :
    (Nat.card K - 1) * Nat.card K ^ (m - 1) *
      (Nat.card K ^ (m + 1) - Nat.card K) ≤ 2 * H.index := by
  let i : Fin (m + 1) := ⟨0, by omega⟩
  let j : Fin (m + 1) := ⟨1, by omega⟩
  have hij : i ≠ j := by
    intro he
    have hz := congrArg Fin.val he
    change (0 : ℕ) = 1 at hz
    omega
  let u : Multiplicative (Space (K := K) (m + 1)) :=
    Multiplicative.ofAdd (offDiagonal K m i j 1)
  have hu : u ≠ 1 := by
    intro he
    apply offDiagonal_ne_zero K m i j hij 1 one_ne_zero
    exact congrArg Multiplicative.toAdd he
  have hnontrivial : projectiveExtensionHom K m hm (SemidirectProduct.inl u) ≠ 1 := by
    rw [projectiveExtensionHom_inl]
    intro he
    apply hu
    apply projectiveUpperHom_injective K m hm
    exact he.trans (projectiveUpperHom K m hm).map_one.symm
  obtain ⟨x, hx⟩ := CFSGConjugateSubgroupDegree.exists_moved_coset_of_ne_one H hH _ hnontrivial
  letI : MulAction (Siegel K m) (elementaryProjective K (m + 1) ⧸ H) :=
    MulAction.compHom _ (projectiveExtensionHom K m hm)
  have hb := degree_bound_of_offDiagonal_motion K m hm x i j 1 hx
  simpa only [Subgroup.index_eq_card] using hb

end SymmetricSubgroupAsymptotics.CFSGSymplecticBinaryHigherSiegelIndex

namespace SymmetricSubgroupAsymptotics.CFSGReduction

open CFSGSymplecticSerreMatrices PrimitiveSocleRawStructure

theorem typeC_binary_higher_siegel_numerator_le_two_mul_proper_index
    (r : ℕ) (hr : 3 ≤ r) (q : CFSG.PrimePower) (hprime : q.prime = 2)
    [IsSimpleGroup (CFSG.Models.C r q)]
    (H : Subgroup (CFSG.Models.C r q)) (hH : H ≠ ⊤) :
    (q.order - 1) * q.order ^ (r - 2) * (q.order ^ r - q.order) ≤ 2 * H.index := by
  obtain ⟨m, rfl⟩ : ∃ m : ℕ, r = m + 1 := ⟨r - 1, by omega⟩
  letI : CharP q.Field 2 := by rw [← hprime]; infer_instance
  let e : CFSG.Models.C (m + 1) q ≃* elementaryProjective q.Field (m + 1) :=
    serreProjectiveEquivElementaryProjective q.Field m
  letI : IsSimpleGroup (elementaryProjective q.Field (m + 1)) := e.symm.isSimpleGroup
  have hmap : H.map e.toMonoidHom ≠ ⊤ := by
    intro ht
    apply hH
    apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
    exact ht.trans (Subgroup.map_top_of_surjective e.toMonoidHom e.surjective).symm
  have hb := CFSGSymplecticBinaryHigherSiegelIndex.projective_two_frame_le_two_mul_proper_index
    q.Field m (by omega) (H.map e.toMonoidHom) hmap
  have hi : (H.map e.toMonoidHom).index = H.index := H.index_map_equiv e
  have hexp : m + 1 - 2 = m - 1 := by omega
  simpa only [q.card_field, hexp, hi] using hb

theorem typeC_binary_higher_siegel_numerator_le_two_mul_leastProperIndex
    (r : ℕ) (hr : 3 ≤ r) (q : CFSG.PrimePower) (hprime : q.prime = 2)
    [IsSimpleGroup (CFSG.Models.C r q)] (ell : ℕ)
    (hell : LeastProperIndex (CFSG.Models.C r q) ell) :
    (q.order - 1) * q.order ^ (r - 2) * (q.order ^ r - q.order) ≤ 2 * ell := by
  obtain ⟨H, hH, he⟩ := hell.1
  exact (typeC_binary_higher_siegel_numerator_le_two_mul_proper_index
    r hr q hprime H hH).trans_eq (congrArg (fun n : ℕ => 2 * n) he)

end SymmetricSubgroupAsymptotics.CFSGReduction
