import SymmetricSubgroupAsymptotics.CFSGPermutationSubsetProductSign
import SymmetricSubgroupAsymptotics.CFSGSymmetricSylowOddElement
import SymmetricSubgroupAsymptotics.CFSGAlternatingSylowEvenIntersection
import SymmetricSubgroupAsymptotics.CFSGPermutationNormalRestriction
import SymmetricSubgroupAsymptotics.CFSGPermutationSylowRestriction

/-! If the complementary set has at least two points, restriction of an
alternating Sylow to an invariant subset is a symmetric Sylow. Parity is
adjusted by an actual pure complementary element of the SAME ambient Sylow. -/
set_option autoImplicit false
noncomputable section
open scoped Classical Pointwise

namespace SymmetricSubgroupAsymptotics.CFSGAlternatingSylowProperRestriction
open Equiv Perm CFSGPermutationSubsetProduct
variable {X : Type*} [Fintype X] [DecidableEq X]

private theorem sign_eq_neg_one {Y : Type*} [Fintype Y] [DecidableEq Y]
    (g : Perm Y) (hg : g ∉ alternatingGroup Y) : sign g = -1 := by
  rcases Int.units_eq_one_or (sign g) with h | h
  · exact False.elim (hg (mem_alternatingGroup.mpr h))
  · exact h

theorem exists_even_split
    (P : Sylow 2 (alternatingGroup X)) (Q : Sylow 2 (Perm X))
    (hPQ : (P : Subgroup (alternatingGroup X)).map (alternatingGroup X).subtype ≤ Q)
    (s : Set X) [Fintype s] [Fintype (sᶜ : Set X)]
    (hQs : (Q : Subgroup (Perm X)) ≤ MulAction.stabilizer (Perm X) s)
    (hcomp : 2 ≤ Nat.card (sᶜ : Set X))
    (a : Perm s) (b : Perm (sᶜ : Set X)) (hab : splitEmbedding s (a, b) ∈ Q) :
    ∃ d : Perm (sᶜ : Set X), splitEmbedding s (a, d) ∈
      (P : Subgroup (alternatingGroup X)).map (alternatingGroup X).subtype := by
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let V := splitSylow s Q hQs
  let R : Sylow 2 (Perm (sᶜ : Set X)) :=
    V.mapSurjective (f := MonoidHom.snd (Perm s) (Perm (sᶜ : Set X)))
      (fun d => ⟨(1, d), rfl⟩)
  obtain ⟨d, hd, hdodd⟩ := CFSGSymmetricSylowOddElement.exists_odd hcomp R
  have hdmap : d ∈ (V : Subgroup (Perm s × Perm (sᶜ : Set X))).map
      (MonoidHom.snd (Perm s) (Perm (sᶜ : Set X))) := hd
  obtain ⟨v, hv, hvd⟩ := hdmap
  have hpure : (1, d) ∈ V := by
    change v.2 = d at hvd
    rw [← hvd]
    exact CFSGSylowProductProjection.snd_pure_mem V hv
  have htQ : splitEmbedding s (1, d) ∈ Q := hpure
  by_cases he : splitEmbedding s (a, b) ∈ alternatingGroup X
  · exact ⟨b, (CFSGAlternatingSylowEvenIntersection.mem_ambient_iff P Q hPQ _).mpr
      ⟨hab, he⟩⟩
  · have hsign : sign (splitEmbedding s (a, b)) = -1 := sign_eq_neg_one _ he
    have hdsign : sign (splitEmbedding s (1, d)) = -1 := by
      rw [sign_splitEmbedding, map_one, one_mul]
      exact sign_eq_neg_one d hdodd
    have hprod : splitEmbedding s (a, b * d) =
        splitEmbedding s (a, b) * splitEmbedding s (1, d) := by
      rw [← map_mul]
      simp only [Prod.mk_mul_mk, mul_one]
    refine ⟨b * d, (CFSGAlternatingSylowEvenIntersection.mem_ambient_iff P Q hPQ _).mpr
      ⟨?_, ?_⟩⟩
    · rw [hprod]
      exact Q.mul_mem hab htQ
    · apply mem_alternatingGroup.mpr
      rw [hprod, map_mul, hsign, hdsign]
      norm_num

omit [Fintype X] in
theorem restrictionHom_split (H : Subgroup (Perm X)) (s : Set X)
    (hHs : H ≤ MulAction.stabilizer (Perm X) s)
    (a : Perm s) (b : Perm (sᶜ : Set X)) (hab : splitEmbedding s (a, b) ∈ H) :
    CFSGPermutationNormalRestriction.restrictionHom H s hHs ⟨splitEmbedding s (a, b), hab⟩ = a := by
  apply Perm.ext
  intro x
  apply Subtype.ext
  exact splitEmbedding_apply_mem s a b x.property

theorem range_eq_restrictedSylow
    (P : Sylow 2 (alternatingGroup X)) (Q : Sylow 2 (Perm X))
    (hPQ : (P : Subgroup (alternatingGroup X)).map (alternatingGroup X).subtype ≤ Q)
    (s : Set X) [Fintype s] [Fintype (sᶜ : Set X)]
    (hQs : (Q : Subgroup (Perm X)) ≤ MulAction.stabilizer (Perm X) s)
    (hcomp : 2 ≤ Nat.card (sᶜ : Set X)) :
    (CFSGPermutationNormalRestriction.restrictionHom
      ((P : Subgroup (alternatingGroup X)).map (alternatingGroup X).subtype) s
      (hPQ.trans hQs)).range =
      (CFSGPermutationSylowRestriction.restrictedSylow Q s hQs : Subgroup (Perm s)) := by
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [CFSGPermutationSylowRestriction.restrictedSylow_coe]
  apply le_antisymm
  · rintro _ ⟨g, rfl⟩
    refine ⟨⟨g.val, hPQ g.property⟩, ?_⟩
    rfl
  · rintro _ ⟨g, rfl⟩
    obtain ⟨⟨a, b⟩, he⟩ := mem_range_of_stabilizes s (hQs g.property)
    have hab : splitEmbedding s (a, b) ∈ Q := he ▸ g.property
    obtain ⟨d, hd⟩ := exists_even_split P Q hPQ s hQs hcomp a b hab
    refine ⟨⟨splitEmbedding s (a, d), hd⟩, ?_⟩
    rw [restrictionHom_split]
    apply Perm.ext
    intro x
    apply Subtype.ext
    change (a x).val = g.val x.val
    rw [← he, splitEmbedding_apply_mem s a b x.property]

end SymmetricSubgroupAsymptotics.CFSGAlternatingSylowProperRestriction
