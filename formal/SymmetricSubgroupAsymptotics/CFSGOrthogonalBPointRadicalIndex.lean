import SymmetricSubgroupAsymptotics.CFSGOrthogonalBPointRadicalStabilizerIndex
import SymmetricSubgroupAsymptotics.CFSGOrthogonalBProjectiveRealization
import SymmetricSubgroupAsymptotics.CFSGSimpleIndexTransport
import SymmetricSubgroupAsymptotics.CFSGConjugateSubgroupDegree
import Mathlib.Algebra.CharP.Lemmas

/-! A nontrivial actual odd-B point-radical element moves a proper
coset by simplicity. Pulling back THAT point stabilizer to the actual
semidirect product gives the whole natural-tail orbit index bound. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalBPointRadicalIndex

open CFSGOrthogonalBSerreMatrices CFSGOrthogonalBPointRadicalHom
open CFSGOrthogonalBPointRadicalExtension CFSGOrthogonalBPointRadicalStabilizerIndex
variable (K : Type) [Field K] [Finite K]

theorem projective_natural_slice_le_proper_index (h2 : (2 : K) ≠ 0) (s : ℕ)
    [IsSimpleGroup (elementaryProjective K (s + 3))]
    (H : Subgroup (elementaryProjective K (s + 3))) (hH : H ≠ ⊤) :
    (Nat.card K ^ (s + 2) - 1) * Nat.card K ^ (s + 2) ≤ H.index := by
  letI : Finite (elementaryProjective K (s + 3)) :=
    Finite.of_surjective (QuotientGroup.mk' (Subgroup.center (elementaryRootGroup K (s + 3))))
      (QuotientGroup.mk'_surjective _)
  let p := ringChar K
  letI : Fact p.Prime := ⟨CharP.prime_ringChar K⟩
  let z : Index (s + 2) → K := Pi.single (pos (s + 2) 0) 1
  have hz : z ≠ 0 := by
    intro he
    have hh := congrFun he (pos (s + 2) 0)
    exact one_ne_zero (by simpa only [z, Pi.single_eq_same, Pi.zero_apply] using hh)
  let u : Multiplicative (Index (s + 2) → K) := Multiplicative.ofAdd z
  have hu : u ≠ 1 := fun he => hz (congrArg Multiplicative.toAdd he)
  have hn : projectiveExtensionHom K s h2 (SemidirectProduct.inl u) ≠ 1 := by
    rw [projectiveExtensionHom_inl]
    intro he
    apply hu
    apply projectiveRadicalHom_injective K h2 s
    exact he.trans (projectiveRadicalHom K h2 s).map_one.symm
  obtain ⟨x, hx⟩ := CFSGConjugateSubgroupDegree.exists_moved_coset_of_ne_one H hH _ hn
  letI : MulAction (PointParabolic K s) (elementaryProjective K (s + 3) ⧸ H) :=
    MulAction.compHom _ (projectiveExtensionHom K s h2)
  have hb := degree_bound_of_radical_motion K h2 p s x z hx
  simpa only [Subgroup.index_eq_card] using hb

end SymmetricSubgroupAsymptotics.CFSGOrthogonalBPointRadicalIndex

namespace SymmetricSubgroupAsymptotics.CFSGReduction

open CFSGOrthogonalBSerreMatrices PrimitiveSocleRawStructure

private theorem pointRadical_two_ne_zero (q : CFSG.PrimePower) (hodd : q.prime ≠ 2) :
    (2 : q.Field) ≠ 0 := by
  intro he
  have hd : q.prime ∣ 2 := (CharP.cast_eq_zero_iff q.Field q.prime 2).mp he
  exact hodd ((Nat.prime_dvd_prime_iff_eq q.prime_isPrime Nat.prime_two).mp hd)

theorem typeB_point_radical_le_proper_index (r : ℕ) (hr : 3 ≤ r) (q : CFSG.PrimePower)
    (hodd : q.prime ≠ 2) [IsSimpleGroup (CFSG.Models.B r q)]
    (H : Subgroup (CFSG.Models.B r q)) (hH : H ≠ ⊤) :
    (q.order ^ (r - 1) - 1) * q.order ^ (r - 1) ≤ H.index := by
  obtain ⟨s, rfl⟩ : ∃ s : ℕ, r = s + 3 := ⟨r - 3, by omega⟩
  have h2 := pointRadical_two_ne_zero q hodd
  let e : CFSG.Models.B (s + 3) q ≃* elementaryProjective q.Field (s + 3) :=
    serreProjectiveEquivElementaryProjective q.Field (s + 2) h2
  letI : IsSimpleGroup (elementaryProjective q.Field (s + 3)) := e.symm.isSimpleGroup
  have hmap : H.map e.toMonoidHom ≠ ⊤ := by
    intro ht
    apply hH
    apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
    exact ht.trans (Subgroup.map_top_of_surjective e.toMonoidHom e.surjective).symm
  have hb := CFSGOrthogonalBPointRadicalIndex.projective_natural_slice_le_proper_index
    q.Field h2 s (H.map e.toMonoidHom) hmap
  have hi : (H.map e.toMonoidHom).index = H.index := H.index_map_equiv e
  have he : s + 3 - 1 = s + 2 := by omega
  simpa only [q.card_field, he, hi] using hb

theorem typeB_point_radical_le_leastProperIndex (r : ℕ) (hr : 3 ≤ r) (q : CFSG.PrimePower)
    (hodd : q.prime ≠ 2) [IsSimpleGroup (CFSG.Models.B r q)] (ell : ℕ)
    (hell : LeastProperIndex (CFSG.Models.B r q) ell) :
    (q.order ^ (r - 1) - 1) * q.order ^ (r - 1) ≤ ell := by
  obtain ⟨H, hH, he⟩ := hell.1
  exact (typeB_point_radical_le_proper_index r hr q hodd H hH).trans_eq he

end SymmetricSubgroupAsymptotics.CFSGReduction
