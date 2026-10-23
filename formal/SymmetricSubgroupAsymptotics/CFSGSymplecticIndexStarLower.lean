import SymmetricSubgroupAsymptotics.CFSGSymplecticIndexStarConjugacy
import SymmetricSubgroupAsymptotics.CFSGSymplecticMinimumIndexLower

/-! The actual original type-C model has proper index at least
q^(rank-1). The larger root star uses only the literal SL double
embedding; rank two retains its already proved initial short root.
This is an action lower bound, not a minimum-index table. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGSymplecticIndexStarLower
open CFSGSymplecticSerreMatrices CFSGSymplecticIndexStarSubgroup
open CFSGSymplecticIndexStarConjugacy

theorem projective_field_power_le_proper_index (K : Type) [Field K] [Finite K]
    (r : ℕ) (hr : 2 ≤ r) [IsSimpleGroup (elementaryProjective K r)]
    (H : Subgroup (elementaryProjective K r)) (hH : H≠⊤) :
    Nat.card K^(r-1) ≤ H.index := by
  by_cases htwo : r=2
  · subst r
    simpa only [Nat.reduceSub,pow_one] using
      CFSGSymplecticSerreMatrices.projective_field_card_le_proper_index K 1 (by decide) H hH
  · obtain ⟨s,rfl⟩ : ∃ s : ℕ, r=s+3 := ⟨r-3,by omega⟩
    letI : Finite (elementaryProjective K (s+3)) :=
      Finite.of_surjective (QuotientGroup.mk' (Subgroup.center (elementaryRootGroup K (s+3))))
        (QuotientGroup.mk'_surjective _)
    letI : Nontrivial (starRoot K s) := Finite.one_lt_card_iff_nontrivial.mp (by
      rw [starRoot_card]
      exact Nat.one_lt_pow (by omega) (Finite.one_lt_card (α:=K)))
    have hh := CFSGConjugateSubgroupDegree.card_le_index_of_nonidentity_conjugate
      (starRoot K s) (star_nonidentity_conjugate K s) H hH
    simpa only [starRoot_card,show s+3-1=s+2 by omega] using hh

end SymmetricSubgroupAsymptotics.CFSGSymplecticIndexStarLower

namespace SymmetricSubgroupAsymptotics.CFSGReduction
open CFSGSymplecticSerreMatrices PrimitiveSocleRawStructure

theorem typeC_field_power_le_proper_index (r : ℕ) (hr : 2 ≤ r) (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.C r q)]
    (H : Subgroup (CFSG.Models.C r q)) (hH : H≠⊤) : q.order^(r-1) ≤ H.index := by
  obtain ⟨s,rfl⟩ : ∃ s : ℕ, r=s+2 := ⟨r-2,by omega⟩
  let e : CFSG.Models.C (s+2) q ≃* elementaryProjective q.Field (s+2) :=
    serreProjectiveEquivElementaryProjective q.Field (s+1)
  letI : IsSimpleGroup (elementaryProjective q.Field (s+2)) := e.symm.isSimpleGroup
  have hmap : H.map e.toMonoidHom≠⊤ := by
    intro ht
    apply hH
    apply top_unique
    intro x _
    have hx : e x∈H.map e.toMonoidHom := by rw [ht]; trivial
    obtain ⟨y,hy,he⟩ := hx
    exact (e.injective he) ▸ hy
  have hh := CFSGSymplecticIndexStarLower.projective_field_power_le_proper_index
    q.Field (s+2) (by omega) (H.map e.toMonoidHom) hmap
  have hi : (H.map e.toMonoidHom).index=H.index := H.index_map_equiv e
  simpa only [q.card_field,hi] using hh

theorem typeC_order_power_le_leastProperIndex (r : ℕ) (hr : 2 ≤ r) (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.C r q)] (ell : ℕ)
    (hell : LeastProperIndex (CFSG.Models.C r q) ell) : q.order^(r-1) ≤ ell := by
  obtain ⟨H,hH,he⟩ := hell.1
  exact (typeC_field_power_le_proper_index r hr q H hH).trans_eq he

end SymmetricSubgroupAsymptotics.CFSGReduction
