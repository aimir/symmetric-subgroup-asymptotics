import SymmetricSubgroupAsymptotics.CFSGGoodSylowPrime
import Mathlib.Data.Fintype.EquivFin
import Mathlib.GroupTheory.SpecificGroups.Alternating

/-! Transport actual two-conjugate Sylow generation through an actual group
isomorphism, and through a literal finite point relabeling. Normalizer
solubility is neither required nor inferred by this generation transport. -/
set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.CFSGConjugateSylowGenerationTransport

theorem exists_generating_conjugates_map {G H : Type*} [Group G] [Group H] [Finite G]
    (e : G ≃* H) {p : ℕ} [Fact p.Prime]
    (h : ∃ (P : Sylow p G) (g : G),
      Subgroup.closure ((P : Set G) ∪
        (P : Subgroup G).map (MulAut.conj g).toMonoidHom) = ⊤) :
    ∃ (Q : Sylow p H) (g : H),
      Subgroup.closure ((Q : Set H) ∪
        (Q : Subgroup H).map (MulAut.conj g).toMonoidHom) = ⊤ := by
  obtain ⟨P, g, hgen⟩ := h
  let Q : Sylow p H := P.mapSurjective (f := e.toMonoidHom) e.surjective
  exact ⟨Q, e g, CFSGReduction.two_conjugates_generate_map e (P : Subgroup G) g hgen⟩

theorem exists_generating_conjugates_relabel {X : Type*} [Fintype X] [DecidableEq X]
    (n : ℕ) (hcard : Fintype.card X = n)
    (h : ∃ (P : Sylow 2 (alternatingGroup X)) (g : alternatingGroup X),
      Subgroup.closure ((P : Set (alternatingGroup X)) ∪
        (P : Subgroup (alternatingGroup X)).map (MulAut.conj g).toMonoidHom) = ⊤) :
    ∃ (Q : Sylow 2 (alternatingGroup (Fin n))) (g : alternatingGroup (Fin n)),
      Subgroup.closure ((Q : Set (alternatingGroup (Fin n))) ∪
        (Q : Subgroup (alternatingGroup (Fin n))).map (MulAut.conj g).toMonoidHom) = ⊤ := by
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact exists_generating_conjugates_map (Fintype.equivFinOfCardEq hcard).altCongrHom h

end SymmetricSubgroupAsymptotics.CFSGConjugateSylowGenerationTransport
