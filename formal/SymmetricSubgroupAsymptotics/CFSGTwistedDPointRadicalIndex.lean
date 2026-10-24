import SymmetricSubgroupAsymptotics.CFSGTwistedDPointRadicalStabilizerIndex
import SymmetricSubgroupAsymptotics.CFSGTwistedDRelativeProjectiveModel
import SymmetricSubgroupAsymptotics.CFSGSimpleIndexTransport
import SymmetricSubgroupAsymptotics.CFSGConjugateSubgroupDegree
import Mathlib.Algebra.CharP.Lemmas

/-! Every original twisted-D proper coset action has a moved actual
point-radical element. The SAME pulled-back stabilizer pays the genuine
fixed-space natural-orbit bound, including the natural-rank-three tail. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGTwistedDPointRadicalIndex

open CFSGTwistedDRelativeElementaryGroup CFSGTwistedDFixedQuadraticSpace
open CFSGTwistedDPointRadicalHom CFSGTwistedDPointRadicalExtension
open CFSGTwistedDPointRadicalStabilizerIndex CFSGTwistedDSingularDimensionBound
open CFSGTwistedA2FixedField

theorem projective_natural_slice_le_proper_index (s : ℕ) (q : CFSG.PrimePower)
    [IsSimpleGroup (relativeRootGroup (s + 2) q ⧸ Subgroup.center (relativeRootGroup (s + 2) q))]
    (H : Subgroup (relativeRootGroup (s + 2) q ⧸ Subgroup.center (relativeRootGroup (s + 2) q)))
    (hH : H ≠ ⊤) : (q.order ^ (s + 2) - 1) * q.order ^ (s + 3) ≤ H.index := by
  letI : Finite (relativeRootGroup (s + 2) q ⧸ Subgroup.center (relativeRootGroup (s + 2) q)) :=
    Finite.of_surjective (QuotientGroup.mk' (Subgroup.center (relativeRootGroup (s + 2) q)))
      (QuotientGroup.mk'_surjective _)
  let p := ringChar (fixedField q)
  letI : CharP (fixedField q) p := ringChar.charP (fixedField q)
  letI : Fact p.Prime := ⟨CharP.prime_ringChar (fixedField q)⟩
  let z := firstAxis (s + 1) q
  have hz : z ≠ 0 := firstAxis_nonzero (s + 1) q
  let u : Multiplicative (fixedSpace (s + 1) q) := Multiplicative.ofAdd z
  have hu : u ≠ 1 := fun he => hz (congrArg Multiplicative.toAdd he)
  have hn : projectiveExtensionHom (s + 1) q (SemidirectProduct.inl u) ≠ 1 := by
    rw [projectiveExtensionHom_inl]
    intro he
    apply hu
    apply projectiveRadicalHom_injective (s + 1) q
    exact he.trans (projectiveRadicalHom (s + 1) q).map_one.symm
  obtain ⟨x, hx⟩ := CFSGConjugateSubgroupDegree.exists_moved_coset_of_ne_one H hH _ hn
  letI : MulAction (PointParabolic s q)
      ((relativeRootGroup (s + 2) q ⧸ Subgroup.center (relativeRootGroup (s + 2) q)) ⧸ H) :=
    MulAction.compHom _ (projectiveExtensionHom (s + 1) q)
  have hb := degree_bound_of_radical_motion s q p x z hx
  simpa only [Subgroup.index_eq_card] using hb

end SymmetricSubgroupAsymptotics.CFSGTwistedDPointRadicalIndex

namespace SymmetricSubgroupAsymptotics.CFSGReduction

open CFSGTwistedDRelativeElementaryGroup CFSGTwistedDRelativeProjectiveModel
open PrimitiveSocleRawStructure

theorem typeTwistedD_point_radical_le_proper_index (r : ℕ) (hr : 4 ≤ r) (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.TwistedD r q)]
    (H : Subgroup (CFSG.Models.TwistedD r q)) (hH : H ≠ ⊤) :
    (q.order ^ (r - 2) - 1) * q.order ^ (r - 1) ≤ H.index := by
  obtain ⟨s, rfl⟩ : ∃ s : ℕ, r = s + 4 := ⟨r - 4, by omega⟩
  let e := originalRelativeProjectiveEquiv s q
  letI : IsSimpleGroup (relativeRootGroup (s + 2) q ⧸ Subgroup.center (relativeRootGroup (s + 2) q)) :=
    e.symm.isSimpleGroup
  have hmap : H.map e.toMonoidHom ≠ ⊤ := by
    intro ht
    apply hH
    apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
    exact ht.trans (Subgroup.map_top_of_surjective e.toMonoidHom e.surjective).symm
  have hb := CFSGTwistedDPointRadicalIndex.projective_natural_slice_le_proper_index s q
    (H.map e.toMonoidHom) hmap
  have hi : (H.map e.toMonoidHom).index = H.index := H.index_map_equiv e
  have h1 : s + 4 - 1 = s + 3 := by omega
  have h2 : s + 4 - 2 = s + 2 := by omega
  simpa only [h1, h2, hi] using hb

theorem typeTwistedD_point_radical_le_leastProperIndex (r : ℕ) (hr : 4 ≤ r) (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.TwistedD r q)] (ell : ℕ)
    (hell : LeastProperIndex (CFSG.Models.TwistedD r q) ell) :
    (q.order ^ (r - 2) - 1) * q.order ^ (r - 1) ≤ ell := by
  obtain ⟨H, hH, he⟩ := hell.1
  exact (typeTwistedD_point_radical_le_proper_index r hr q H hH).trans_eq he

end SymmetricSubgroupAsymptotics.CFSGReduction
