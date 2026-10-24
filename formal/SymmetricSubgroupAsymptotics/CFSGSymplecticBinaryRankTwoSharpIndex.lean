import SymmetricSubgroupAsymptotics.CFSGSymplecticBinarySiegelSharpIndex
import SymmetricSubgroupAsymptotics.CFSGSymplecticBinaryRankTwoIndex

/-! The sharper uniform orbit estimate applies to the SAME original
simple C2 model in characteristic two. It proves q(q-1)^2<=2[ G:H ]
without a field threshold, and q²<=[ G:H ] for q>=4. The q=4 class-count
capacity is not asserted or assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGSymplecticBinaryRankTwoSharpIndex

open BinarySymmetricSquareAction CFSGSymplecticSerreMatrices
open CFSGSymplecticRankTwoSiegelEmbedding CFSGSymplecticRankTwoSiegelExtension
open CFSGSymplecticBinarySiegelStabilizerIndex
variable (K : Type) [Field K] [Finite K] [CharP K 2]

theorem projective_field_mul_square_sub_one_le_twice_proper_index
    [IsSimpleGroup (elementaryProjective K 2)]
    (H : Subgroup (elementaryProjective K 2)) (hH : H ≠ ⊤) :
    Nat.card K * (Nat.card K - 1) ^ 2 ≤ 2 * H.index := by
  let u : Multiplicative (Space (K := K)) := Multiplicative.ofAdd (offDiagonal K 1)
  have hu : u ≠ 1 := by
    intro he
    apply offDiagonal_ne_zero K 1 one_ne_zero
    exact congrArg Multiplicative.toAdd he
  have hnontrivial : projectiveExtensionHom K (SemidirectProduct.inl u) ≠ 1 := by
    rw [projectiveExtensionHom_inl]
    intro he
    apply hu
    apply projectiveUpperHom_injective K
    exact he.trans (projectiveUpperHom K).map_one.symm
  obtain ⟨x, hx⟩ := CFSGConjugateSubgroupDegree.exists_moved_coset_of_ne_one H hH _ hnontrivial
  letI : MulAction (Siegel K) (elementaryProjective K 2 ⧸ H) :=
    MulAction.compHom _ (projectiveExtensionHom K)
  have hb := CFSGSymplecticBinarySiegelSharpIndex.degree_bound_of_offDiagonal_motion K x 1 hx
  simpa only [Subgroup.index_eq_card] using hb

private theorem square_le_of_scaled_bound (q n : ℕ) (hq : 4 ≤ q)
    (h : q * (q - 1) ^ 2 ≤ 2 * n) : q ^ 2 ≤ n := by
  have hq3 : 3 ≤ q - 1 := by omega
  have hm := Nat.mul_le_mul_right (q - 1) hq3
  rw [← pow_two] at hm
  have hsquare : 2 * q ≤ (q - 1) ^ 2 := by omega
  have hlow : 2 * q ^ 2 ≤ 2 * n := by
    calc
      _ = q * (2 * q) := by ring
      _ ≤ q * (q - 1) ^ 2 := Nat.mul_le_mul_left _ hsquare
      _ ≤ _ := h
  exact Nat.le_of_mul_le_mul_left hlow (by decide : 0 < 2)

theorem projective_field_square_le_proper_index (hq : 4 ≤ Nat.card K)
    [IsSimpleGroup (elementaryProjective K 2)]
    (H : Subgroup (elementaryProjective K 2)) (hH : H ≠ ⊤) :
    Nat.card K ^ 2 ≤ H.index :=
  square_le_of_scaled_bound _ _ hq
    (projective_field_mul_square_sub_one_le_twice_proper_index K H hH)

end SymmetricSubgroupAsymptotics.CFSGSymplecticBinaryRankTwoSharpIndex

namespace SymmetricSubgroupAsymptotics.CFSGReduction

open CFSGSymplecticSerreMatrices PrimitiveSocleRawStructure

theorem typeC_rankTwo_binary_field_mul_square_sub_one_le_twice_proper_index
    (q : CFSG.PrimePower) (hchar : q.prime = 2)
    [IsSimpleGroup (CFSG.Models.C 2 q)]
    (H : Subgroup (CFSG.Models.C 2 q)) (hH : H ≠ ⊤) :
    q.order * (q.order - 1) ^ 2 ≤ 2 * H.index := by
  letI : CharP q.Field 2 := by rw [← hchar]; infer_instance
  let e : CFSG.Models.C 2 q ≃* elementaryProjective q.Field 2 :=
    serreProjectiveEquivElementaryProjective q.Field 1
  letI : IsSimpleGroup (elementaryProjective q.Field 2) := e.symm.isSimpleGroup
  have hmap : H.map e.toMonoidHom ≠ ⊤ := by
    intro ht
    apply hH
    apply top_unique
    intro x _
    have hx : e x ∈ H.map e.toMonoidHom := by rw [ht]; trivial
    obtain ⟨y, hy, he⟩ := hx
    exact (e.injective he) ▸ hy
  have hb := CFSGSymplecticBinaryRankTwoSharpIndex.projective_field_mul_square_sub_one_le_twice_proper_index
    q.Field (H.map e.toMonoidHom) hmap
  have hi : (H.map e.toMonoidHom).index = H.index := H.index_map_equiv e
  simpa only [q.card_field, hi] using hb

theorem typeC_rankTwo_binary_field_square_le_proper_index_of_four_le
    (q : CFSG.PrimePower) (hchar : q.prime = 2) (hq : 4 ≤ q.order)
    [IsSimpleGroup (CFSG.Models.C 2 q)]
    (H : Subgroup (CFSG.Models.C 2 q)) (hH : H ≠ ⊤) : q.order ^ 2 ≤ H.index := by
  letI : CharP q.Field 2 := by rw [← hchar]; infer_instance
  let e : CFSG.Models.C 2 q ≃* elementaryProjective q.Field 2 :=
    serreProjectiveEquivElementaryProjective q.Field 1
  letI : IsSimpleGroup (elementaryProjective q.Field 2) := e.symm.isSimpleGroup
  have hmap : H.map e.toMonoidHom ≠ ⊤ := by
    intro ht
    apply hH
    apply top_unique
    intro x _
    have hx : e x ∈ H.map e.toMonoidHom := by rw [ht]; trivial
    obtain ⟨y, hy, he⟩ := hx
    exact (e.injective he) ▸ hy
  have hb := CFSGSymplecticBinaryRankTwoSharpIndex.projective_field_square_le_proper_index
    q.Field (by simpa only [q.card_field] using hq) (H.map e.toMonoidHom) hmap
  have hi : (H.map e.toMonoidHom).index = H.index := H.index_map_equiv e
  simpa only [q.card_field, hi] using hb

theorem typeC_rankTwo_binary_order_square_le_leastProperIndex_of_four_le
    (q : CFSG.PrimePower) (hchar : q.prime = 2) (hq : 4 ≤ q.order)
    [IsSimpleGroup (CFSG.Models.C 2 q)] (ell : ℕ)
    (hell : LeastProperIndex (CFSG.Models.C 2 q) ell) : q.order ^ 2 ≤ ell := by
  obtain ⟨H, hH, he⟩ := hell.1
  exact (typeC_rankTwo_binary_field_square_le_proper_index_of_four_le q hchar hq H hH).trans_eq he

end SymmetricSubgroupAsymptotics.CFSGReduction
