import SymmetricSubgroupAsymptotics.CFSGOrthogonalDPointRadicalStabilizerIndex
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDProjectiveRealization
import SymmetricSubgroupAsymptotics.CFSGSimpleIndexTransport
import SymmetricSubgroupAsymptotics.CFSGConjugateSubgroupDegree
import Mathlib.Algebra.CharP.Lemmas

/-! A literal nontrivial point-radical element moves an actual proper
coset by simplicity. The SAME pulled-back stabilizer then pays the full
natural tail-orbit lower bound, for every original D proper subgroup. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDPointRadicalIndex

open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDPointRadicalHom
open CFSGOrthogonalDPointRadicalExtension CFSGOrthogonalDPointRadicalStabilizerIndex
variable (K : Type) [Field K] [Finite K]

theorem projective_natural_slice_le_proper_index (s : ℕ)
    [IsSimpleGroup (elementaryProjective K (s + 4))]
    (H : Subgroup (elementaryProjective K (s + 4))) (hH : H ≠ ⊤) :
    (Nat.card K ^ (s + 3) - 1) * Nat.card K ^ (s + 2) ≤ H.index := by
  letI : Finite (elementaryProjective K (s + 4)) :=
    Finite.of_surjective (QuotientGroup.mk' (Subgroup.center (elementaryRootGroup K (s + 4))))
      (QuotientGroup.mk'_surjective _)
  let p := ringChar K
  letI : Fact p.Prime := ⟨CharP.prime_ringChar K⟩
  let z : Index (s + 3) → K := Pi.single (Sum.inl 0) 1
  have hz : z ≠ 0 := by
    intro he
    have h := congrFun he (Sum.inl 0)
    exact one_ne_zero (by simpa only [z, Pi.single_eq_same, Pi.zero_apply] using h)
  let u : Multiplicative (Index (s + 3) → K) := Multiplicative.ofAdd z
  have hu : u ≠ 1 := fun he => hz (congrArg Multiplicative.toAdd he)
  have hnontrivial : projectiveExtensionHom K (s + 1) (SemidirectProduct.inl u) ≠ 1 := by
    rw [projectiveExtensionHom_inl]
    intro he
    apply hu
    apply projectiveRadicalHom_injective K (s + 1)
    exact he.trans (projectiveRadicalHom K (s + 1)).map_one.symm
  obtain ⟨x, hx⟩ := CFSGConjugateSubgroupDegree.exists_moved_coset_of_ne_one H hH _ hnontrivial
  letI : MulAction (PointParabolic K (s + 1)) (elementaryProjective K (s + 4) ⧸ H) :=
    MulAction.compHom _ (projectiveExtensionHom K (s + 1))
  have hb := degree_bound_of_radical_motion K p (s + 1) x z hx
  simpa only [Subgroup.index_eq_card] using hb

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDPointRadicalIndex

namespace SymmetricSubgroupAsymptotics.CFSGReduction

open CFSGOrthogonalDSerreMatrices PrimitiveSocleRawStructure

theorem typeD_point_radical_le_proper_index (r : ℕ) (hr : 4 ≤ r) (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.D r q)]
    (H : Subgroup (CFSG.Models.D r q)) (hH : H ≠ ⊤) :
    (q.order ^ (r - 1) - 1) * q.order ^ (r - 2) ≤ H.index := by
  obtain ⟨s, rfl⟩ : ∃ s : ℕ, r = s + 4 := ⟨r - 4, by omega⟩
  let e : CFSG.Models.D (s + 4) q ≃* elementaryProjective q.Field (s + 4) :=
    serreProjectiveEquivElementaryProjective q.Field s
  letI : IsSimpleGroup (elementaryProjective q.Field (s + 4)) := e.symm.isSimpleGroup
  have hmap : H.map e.toMonoidHom ≠ ⊤ := by
    intro ht
    apply hH
    apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
    exact ht.trans (Subgroup.map_top_of_surjective e.toMonoidHom e.surjective).symm
  have hb := CFSGOrthogonalDPointRadicalIndex.projective_natural_slice_le_proper_index
    q.Field s (H.map e.toMonoidHom) hmap
  have hi : (H.map e.toMonoidHom).index = H.index := H.index_map_equiv e
  have h1 : s + 4 - 1 = s + 3 := by omega
  have h2 : s + 4 - 2 = s + 2 := by omega
  simpa only [q.card_field, h1, h2, hi] using hb

theorem typeD_point_radical_le_leastProperIndex (r : ℕ) (hr : 4 ≤ r) (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.D r q)] (ell : ℕ)
    (hell : LeastProperIndex (CFSG.Models.D r q) ell) :
    (q.order ^ (r - 1) - 1) * q.order ^ (r - 2) ≤ ell := by
  obtain ⟨H, hH, he⟩ := hell.1
  exact (typeD_point_radical_le_proper_index r hr q H hH).trans_eq he

end SymmetricSubgroupAsymptotics.CFSGReduction
