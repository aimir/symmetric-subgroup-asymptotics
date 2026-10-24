import SymmetricSubgroupAsymptotics.CFSGSymplecticBinarySiegelStabilizerIndex
import SymmetricSubgroupAsymptotics.CFSGSymplecticProjectiveRealization
import SymmetricSubgroupAsymptotics.CFSGSimpleIndexTransport
import SymmetricSubgroupAsymptotics.CFSGConjugateSubgroupDegree

/-! Every proper subgroup of the SAME original simple C2 model has
index at least q² in characteristic two for q at least eight. The
constructed actual Siegel extension acts on the actual coset carrier;
its literal off-diagonal parameter moves a coset by simplicity. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGSymplecticBinaryRankTwoIndex

open BinarySymmetricSquareAction CFSGSymplecticSerreMatrices
open CFSGSymplecticRankTwoSiegelEmbedding CFSGSymplecticRankTwoSiegelExtension
open CFSGSymplecticBinarySiegelStabilizerIndex
variable (K : Type) [Field K] [Finite K] [CharP K 2]

/-- The stabilizer is the actual point stabilizer of the given action. -/
theorem degree_le_of_offDiagonal_motion (hq : 8 ≤ Nat.card K)
    {X : Type*} [Finite X] [MulAction (Siegel K) X]
    (x : X) (t : K)
    (hx : (SemidirectProduct.inl (Multiplicative.ofAdd (offDiagonal K t)) : Siegel K) • x ≠ x) :
    Nat.card K ^ 2 ≤ Nat.card X := by
  let M := MulAction.stabilizer (Siegel K) x
  have ht : (SemidirectProduct.inl (Multiplicative.ofAdd (offDiagonal K t)) : Siegel K) ∉ M := hx
  have hb := field_square_le_index K hq M t ht
  have ho : M.index = Nat.card (MulAction.orbit (Siegel K) x) :=
    (Nat.card_congr (MulAction.orbitEquivQuotientStabilizer (Siegel K) x)).symm
  rw [ho] at hb
  exact hb.trans (Nat.card_le_card_of_injective
    (fun y : MulAction.orbit (Siegel K) x => y.val) Subtype.val_injective)

theorem projective_field_square_le_proper_index (hq : 8 ≤ Nat.card K)
    [IsSimpleGroup (elementaryProjective K 2)]
    (H : Subgroup (elementaryProjective K 2)) (hH : H ≠ ⊤) :
    Nat.card K ^ 2 ≤ H.index := by
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
  have hb := degree_le_of_offDiagonal_motion K hq x 1 hx
  simpa only [Subgroup.index_eq_card] using hb

end SymmetricSubgroupAsymptotics.CFSGSymplecticBinaryRankTwoIndex

namespace SymmetricSubgroupAsymptotics.CFSGReduction

open CFSGSymplecticSerreMatrices PrimitiveSocleRawStructure

theorem typeC_rankTwo_binary_field_square_le_proper_index (q : CFSG.PrimePower)
    (hchar : q.prime = 2) (hq : 8 ≤ q.order)
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
  have hb := CFSGSymplecticBinaryRankTwoIndex.projective_field_square_le_proper_index
    q.Field (by simpa only [q.card_field] using hq) (H.map e.toMonoidHom) hmap
  have hi : (H.map e.toMonoidHom).index = H.index := H.index_map_equiv e
  simpa only [q.card_field, hi] using hb

theorem typeC_rankTwo_binary_order_square_le_leastProperIndex (q : CFSG.PrimePower)
    (hchar : q.prime = 2) (hq : 8 ≤ q.order)
    [IsSimpleGroup (CFSG.Models.C 2 q)] (ell : ℕ)
    (hell : LeastProperIndex (CFSG.Models.C 2 q) ell) : q.order ^ 2 ≤ ell := by
  obtain ⟨H, hH, he⟩ := hell.1
  exact (typeC_rankTwo_binary_field_square_le_proper_index q hchar hq H hH).trans_eq he

end SymmetricSubgroupAsymptotics.CFSGReduction
