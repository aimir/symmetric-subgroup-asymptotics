import SymmetricSubgroupAsymptotics.CFSGTwistedDIndexStarSubgroup
import SymmetricSubgroupAsymptotics.CFSGTypeAColumnRootConjugacy
import SymmetricSubgroupAsymptotics.CFSGConjugateSubgroupDegree
import SymmetricSubgroupAsymptotics.CFSGSimpleIndexTransport

/-! The original twisted-D least index is at least q^(r-2). The
retained SL star has all nonidentity elements conjugate in the SAME
original relative central quotient. The Burnside degree lemma applies
there directly; no faithful action of a PSL quotient is presumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTwistedDIndexStarLower
open CFSGTwistedDRelativeElementaryGroup CFSGTwistedDIndexStarSubgroup
open CFSGTwistedDRelativeProjectiveModel CFSGTwistedDProjectiveUnipotent CFSGTwistedA2FixedField
open CFSGTypeAProjectivePointRoots CFSGTypeAColumnRootConjugacy CFSGTypeABlockEmbedding

theorem star_nonidentity_conjugate (s : ℕ) (q : CFSG.PrimePower)
    (a b : starRoot s q) (ha : a ≠ 1) (hb : b ≠ 1) :
    ∃ z : Projective s q, z * (a : Projective s q) * z⁻¹ = b := by
  obtain ⟨f, hf⟩ := a.property
  obtain ⟨g, hg⟩ := b.property
  have hf0 : f.toAdd ≠ 0 := by
    intro he
    apply ha
    apply Subtype.ext
    rw [← hf, show f = 1 from congrArg Multiplicative.ofAdd he, map_one]
    rfl
  have hg0 : g.toAdd ≠ 0 := by
    intro he
    apply hb
    apply Subtype.ext
    rw [← hg, show g = 1 from congrArg Multiplicative.ofAdd he, map_one]
    rfl
  obtain ⟨A, hA⟩ := exists_form_conjugator
    (F := fixedField q) (0 : Fin (s + 2)) (⟨1, by omega⟩ : Fin (s + 2))
    (by intro he; have hv := congrArg Fin.val he; change 0 = 1 at hv; omega)
    f.toAdd g.toAdd hf0 hg0
  let pi := QuotientGroup.mk' (Subgroup.center (relativeRootGroup (s + 2) q))
  let j := pi.comp (starEmbedding s q)
  refine ⟨j A, ?_⟩
  rw [← hf, ← hg]
  change j A * j (transvectionSL f.toAdd.property) * (j A)⁻¹ = j (transvectionSL g.toAdd.property)
  have he := congrArg j hA
  simpa only [map_mul, map_inv] using he

theorem projective_field_power_le_proper_index (s : ℕ) (q : CFSG.PrimePower)
    [IsSimpleGroup (Projective s q)] (H : Subgroup (Projective s q)) (hH : H ≠ ⊤) :
    q.order ^ (s + 2) ≤ H.index := by
  letI : Finite (Projective s q) :=
    Finite.of_surjective (QuotientGroup.mk' (Subgroup.center (relativeRootGroup (s + 2) q)))
      (QuotientGroup.mk'_surjective _)
  letI : Nontrivial (starRoot s q) := Finite.one_lt_card_iff_nontrivial.mp (by
    rw [starRoot_card]
    exact Nat.one_lt_pow (by omega)
      (lt_of_lt_of_le (by decide : 1 < 2) (CFSGTwistedAQuadraticTrace.order_two_le q)))
  have h := CFSGConjugateSubgroupDegree.card_le_index_of_nonidentity_conjugate
    (starRoot s q) (star_nonidentity_conjugate s q) H hH
  rwa [starRoot_card] at h

theorem original_field_power_le_leastProperIndex (s : ℕ) (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.TwistedD (s + 4) q)] (ell : ℕ)
    (hell : PrimitiveSocleRawStructure.LeastProperIndex (CFSG.Models.TwistedD (s + 4) q) ell) :
    q.order ^ (s + 2) ≤ ell := by
  let e := originalRelativeProjectiveEquiv s q
  letI : IsSimpleGroup (Projective s q) := e.symm.isSimpleGroup
  obtain ⟨H, hH, hi⟩ := (CFSGReduction.leastProperIndex_of_mulEquiv e ell hell).1
  have h := projective_field_power_le_proper_index s q H hH
  rwa [hi] at h

end SymmetricSubgroupAsymptotics.CFSGTwistedDIndexStarLower

namespace SymmetricSubgroupAsymptotics.CFSGReduction
open PrimitiveSocleRawStructure

theorem typeTwistedD_order_power_le_leastProperIndex (r : ℕ) (hr : 4 ≤ r) (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.TwistedD r q)] (ell : ℕ)
    (hell : LeastProperIndex (CFSG.Models.TwistedD r q) ell) : q.order ^ (r - 2) ≤ ell := by
  obtain ⟨s, rfl⟩ : ∃ s : ℕ, r = s + 4 := ⟨r - 4, by omega⟩
  simpa only [show s + 4 - 2 = s + 2 by omega] using
    CFSGTwistedDIndexStarLower.original_field_power_le_leastProperIndex s q ell hell

end SymmetricSubgroupAsymptotics.CFSGReduction
