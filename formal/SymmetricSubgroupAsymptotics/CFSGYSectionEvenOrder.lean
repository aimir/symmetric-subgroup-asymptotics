import SymmetricSubgroupAsymptotics.CFSGInvolutionDerivedEvenOrder
import SymmetricSubgroupAsymptotics.CFSGYSectionGeneration

/-! Uniform parity for the actual central quotients of Y-derived groups.
The nonadjacency graph is connected for every triple of arms of length
at least two. Odd-order quotients of the derived subgroup are therefore
trivial. No catalogue order or simplicity certificate is used. -/
set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.CFSGReduction
open CFSGGeneration CFSG.Models.YGroups

def yNonadjacent (arms : Arms) (i j : Node arms) : Prop :=
  i ≠ j ∧ ¬ Adjacent arms i j

theorem y_nonadjacent_connected (arms : Arms) (i : Node arms) :
    Relation.ReflTransGen (yNonadjacent arms) none i := by
  cases i with
  | none => exact Relation.ReflTransGen.refl
  | some q =>
    rcases q with ⟨a, d⟩
    by_cases hd : d.val = 0
    · obtain ⟨c, hc⟩ := exists_ne a
      let v : Node arms := near arms c 1
      have hnv : yNonadjacent arms none v := by
        constructor
        · simp [v, near]
        · simp [Adjacent, v, near]
      have hvq : yNonadjacent arms v (some ⟨a,d⟩) := by
        constructor
        · intro he
          have hca : c = a := congrArg (fun x : Node arms =>
            match x with | none => (0 : Fin 3) | some q => q.1) he
          exact hc hca
        · dsimp only [Adjacent, v, near]
          exact fun h => hc h.1
      exact (Relation.ReflTransGen.single hnv).tail hvq
    · exact Relation.ReflTransGen.single ⟨by simp, hd⟩

theorem y_abelianization_generators_equal (arms : Arms) (i : Node arms) :
    Abelianization.of (PresentedGroup.of (rels := relations arms) i) =
      Abelianization.of (PresentedGroup.of (rels := relations arms) none) := by
  have heq (i j : Node arms) (hij : Adjacent arms i j) :
      Abelianization.of (PresentedGroup.of (rels := relations arms) i) =
        Abelianization.of (PresentedGroup.of (rels := relations arms) j) := by
    apply commutative_involutions_eq_of_product_cube
    · simp only [← map_pow, y_generator_sq, map_one]
    · simp only [← map_pow, y_generator_sq, map_one]
    · simp only [← map_mul, ← map_pow, y_adjacent_product_cube arms i j hij, map_one]
  have hpath : ∀ {i j}, Relation.ReflTransGen (Adjacent arms) i j →
      Abelianization.of (PresentedGroup.of (rels := relations arms) i) =
        Abelianization.of (PresentedGroup.of (rels := relations arms) j) := by
    intro i j h
    induction h with
    | refl => rfl
    | tail _ hlast ih => exact ih.trans (heq _ _ hlast)
  exact (hpath (y_connected arms i)).symm

theorem y_nonadjacent_product_sq (arms : Arms) (i j : Node arms)
    (hij : yNonadjacent arms i j) :
    (PresentedGroup.of (rels := relations arms) i * PresentedGroup.of j) ^ 2 = 1 := by
  have h := PresentedGroup.one_of_mem (rels := relations arms)
    (x := (FreeGroup.of i * FreeGroup.of j) ^ 2)
    (Or.inr (Or.inr (Or.inl ⟨i,j,hij.1,hij.2,rfl⟩)))
  simpa only [map_pow, map_mul, PresentedGroup.of] using h

theorem y_simpleSection_even_card (arms : Arms)
    (hn : ¬ IsMulCommutative (SimpleSection arms)) :
    Even (Nat.card (SimpleSection arms)) := by
  exact even_card_of_derived_involution_quotient
    (PresentedGroup.of (rels := relations arms)) none
    (PresentedGroup.closure_range_of _)
    (fun i => by simpa only [pow_two] using y_generator_sq arms i)
    (y_abelianization_generators_equal arms)
    (yNonadjacent arms) (y_nonadjacent_product_sq arms)
    (y_nonadjacent_connected arms) (QuotientGroup.mk' _)
    (QuotientGroup.mk'_surjective _) hn

end SymmetricSubgroupAsymptotics.CFSGReduction
