import SymmetricSubgroupAsymptotics.CFSGSymplecticHeisenbergExtension
import SymmetricSubgroupAsymptotics.CFSGHeisenbergSLTwoActionIndex
import SymmetricSubgroupAsymptotics.CFSGSymplecticProjectiveRealization
import SymmetricSubgroupAsymptotics.CFSGSimpleIndexTransport
import Mathlib.FieldTheory.Finite.Basic

/-! Every proper subgroup of the SAME original simple C2 model has
index at least q squared in odd characteristic. The actual Heisenberg
semidirect tail SL2 maps to the original matrix quotient. Its literal
long centre moves a proper coset by simplicity, and the proved coupled
stabilizer theorem bounds the degree of that actual action. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGSymplecticOddRankTwoIndex

open CFSGHeisenbergCoordinateGroup CFSGHeisenbergSLTwoStabilizers
open CFSGSymplecticSerreMatrices CFSGSymplecticHeisenbergEmbedding
open CFSGSymplecticHeisenbergTail CFSGSymplecticHeisenbergExtension CFSGTypeASLTwoWeyl
variable (K : Type) [Field K]

theorem coordinate_action (hTwo : (2 : K) ≠ 0) (A : SL2 (F := K)) (g : Element K 1) :
    coordinateVector (tailAction K hTwo A g) =
      (A⁻¹).transpose.toLin' (coordinateVector g) := by
  rw [tailAction_apply, Matrix.SpecialLinearGroup.toLin'_apply, Matrix.toLin'_apply,
    Matrix.SpecialLinearGroup.coe_transpose, Matrix.SpecialLinearGroup.coe_inv,
    Matrix.adjugate_fin_two]
  ext i
  fin_cases i <;>
    simp [coordinateVector, transform, Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;> ring

theorem projective_field_square_le_proper_index [Finite K] (hTwo : (2 : K) ≠ 0)
    [IsSimpleGroup (elementaryProjective K 2)]
    (H : Subgroup (elementaryProjective K 2)) (hH : H ≠ ⊤) : Nat.card K ^ 2 ≤ H.index := by
  letI : Fintype K := Fintype.ofFinite K
  obtain ⟨p, hchar, n, hp, _hn⟩ := FiniteField.card' K
  letI : CharP K p := hchar
  letI : Fact p.Prime := ⟨hp⟩
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
  have hb := CFSGHeisenbergSLTwoActionIndex.degree_le_of_central_motion p
    (tailAction K hTwo) (coordinate_action K hTwo) x (Multiplicative.ofAdd (1 : K)) hx
  simpa only [Subgroup.index_eq_card] using hb

end SymmetricSubgroupAsymptotics.CFSGSymplecticOddRankTwoIndex

namespace SymmetricSubgroupAsymptotics.CFSGReduction
open CFSGSymplecticSerreMatrices PrimitiveSocleRawStructure

theorem typeC_rankTwo_field_square_le_proper_index (q : CFSG.PrimePower)
    (hTwo : (2 : q.Field) ≠ 0) [IsSimpleGroup (CFSG.Models.C 2 q)]
    (H : Subgroup (CFSG.Models.C 2 q)) (hH : H ≠ ⊤) : q.order ^ 2 ≤ H.index := by
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
  have hh := CFSGSymplecticOddRankTwoIndex.projective_field_square_le_proper_index
    q.Field hTwo (H.map e.toMonoidHom) hmap
  have hi : (H.map e.toMonoidHom).index = H.index := H.index_map_equiv e
  simpa only [q.card_field, hi] using hh

theorem typeC_rankTwo_order_square_le_leastProperIndex (q : CFSG.PrimePower)
    (hTwo : (2 : q.Field) ≠ 0) [IsSimpleGroup (CFSG.Models.C 2 q)] (ell : ℕ)
    (hell : LeastProperIndex (CFSG.Models.C 2 q) ell) : q.order ^ 2 ≤ ell := by
  obtain ⟨H, hH, he⟩ := hell.1
  exact (typeC_rankTwo_field_square_le_proper_index q hTwo H hH).trans_eq he

end SymmetricSubgroupAsymptotics.CFSGReduction
