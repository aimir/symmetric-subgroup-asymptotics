import SymmetricSubgroupAsymptotics.CFSGSporadicGeneration
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-! A finite family of fixed concrete group types has a uniform finite
generation bound on its finite members. No order formula, identification,
simplicity, or global finiteness of the family members is assumed. This
provides a polynomial automorphism bound; it does not prove two-generation. -/
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators
namespace SymmetricSubgroupAsymptotics.CFSGGeneration
universe u v w

/-- Infinite members contribute zero. The theorem below applies only after
an actual `Finite` instance has been supplied for the selected member. -/
def familyGenerationDegree {ι : Type u} [Fintype ι] (M : ι → Type v) : ℕ :=
  ∑ i, Nat.card (M i)

theorem finite_generators_of_card (G : Type v) [Group G] [Finite G] :
    ∃ S : Finset G, Subgroup.closure (S : Set G) = ⊤ ∧ S.card ≤ Nat.card G := by
  letI finiteFamilyGeneration_fintype : Fintype G := Fintype.ofFinite G
  refine ⟨Finset.univ, ?_, ?_⟩
  · simpa only [Finset.coe_univ] using (Subgroup.closure_univ (G := G))
  · simp only [Finset.card_univ, Nat.card_eq_fintype_card]
    exact le_rfl

theorem family_generators {ι : Type u} [Fintype ι]
    (M : ι → Type v) [∀ i, Group (M i)] (i : ι) [Finite (M i)] :
    ∃ S : Finset (M i), Subgroup.closure (S : Set (M i)) = ⊤ ∧
      S.card ≤ familyGenerationDegree M := by
  obtain ⟨S, hS, hcard⟩ := finite_generators_of_card (M i)
  refine ⟨S, hS, hcard.trans ?_⟩
  exact Finset.single_le_sum (fun j _ => Nat.zero_le (Nat.card (M j)))
    (Finset.mem_univ i)

theorem hom_card_le_pow_of_generators {G : Type v} {H : Type w}
    [Group G] [Group H] [Finite H] (S : Finset G)
    (hS : Subgroup.closure (S : Set G) = ⊤) :
    Nat.card (G →* H) ≤ Nat.card H ^ S.card := by
  let evaluate : (G →* H) → (S → H) := fun f s => f s
  have he : Function.Injective evaluate := by
    intro f g h
    apply MonoidHom.eq_of_eqOn_dense hS
    intro s hs
    exact congrFun h ⟨s, hs⟩
  calc
    Nat.card (G →* H) ≤ Nat.card (S → H) := Nat.card_le_card_of_injective evaluate he
    _ = Nat.card H ^ S.card := by
      rw [Nat.card_fun, Nat.card_eq_fintype_card (α := S), Fintype.card_coe]

theorem aut_card_le_pow_of_generators {G : Type v} [Group G] [Finite G]
    (S : Finset G) (hS : Subgroup.closure (S : Set G) = ⊤) {d : ℕ}
    (hcard : S.card ≤ d) : Nat.card (G ≃* G) ≤ Nat.card G ^ d := by
  letI finiteFamilyGeneration_homs : Finite (G →* G) :=
    Finite.of_injective (fun f : G →* G => (f : G → G)) DFunLike.coe_injective
  calc
    Nat.card (G ≃* G) ≤ Nat.card (G →* G) :=
      Nat.card_le_card_of_injective (fun a => a.toMonoidHom)
        (fun _ _ h => MulEquiv.ext (fun x => DFunLike.congr_fun h x))
    _ ≤ Nat.card G ^ S.card := hom_card_le_pow_of_generators S hS
    _ ≤ Nat.card G ^ d := Nat.pow_le_pow_right (Nat.card_pos (α := G)) hcard

theorem family_aut_card_le_pow {ι : Type u} [Fintype ι]
    (M : ι → Type v) [∀ i, Group (M i)] (i : ι) [Finite (M i)] :
    Nat.card (M i ≃* M i) ≤ Nat.card (M i) ^ familyGenerationDegree M := by
  obtain ⟨S, hS, hcard⟩ := family_generators M i
  exact aut_card_le_pow_of_generators S hS hcard

/-- The same constant applies to the original finite group, using the actual
isomorphism to one fixed family member. -/
theorem family_generators_of_mulEquiv {ι : Type u} [Fintype ι]
    (M : ι → Type v) [∀ i, Group (M i)] {G : Type w} [Group G] [Finite G]
    (i : ι) (e : G ≃* M i) :
    ∃ S : Finset G, Subgroup.closure (S : Set G) = ⊤ ∧
      S.card ≤ familyGenerationDegree M := by
  letI finiteFamilyGeneration_selected : Finite (M i) := Finite.of_equiv G e.toEquiv
  obtain ⟨S, hS, hcard⟩ := family_generators M i
  refine ⟨S.image e.symm, ?_, Finset.card_image_le.trans hcard⟩
  rw [Finset.coe_image]
  change Subgroup.closure (e.symm.toMonoidHom '' (S : Set (M i))) = ⊤
  rw [← MonoidHom.map_closure, hS]
  exact Subgroup.map_top_of_surjective e.symm.toMonoidHom e.symm.surjective

theorem family_aut_card_le_pow_of_mulEquiv {ι : Type u} [Fintype ι]
    (M : ι → Type v) [∀ i, Group (M i)] {G : Type w} [Group G] [Finite G]
    (i : ι) (e : G ≃* M i) :
    Nat.card (G ≃* G) ≤ Nat.card G ^ familyGenerationDegree M := by
  obtain ⟨S, hS, hcard⟩ := family_generators_of_mulEquiv M i e
  exact aut_card_le_pow_of_generators S hS hcard

abbrev sporadicGenerationDegree : ℕ := familyGenerationDegree CFSG.Sporadic.Model

theorem sporadic_generators (s : CFSG.Sporadic) [Finite s.Model] :
    ∃ S : Finset s.Model, Subgroup.closure (S : Set s.Model) = ⊤ ∧
      S.card ≤ sporadicGenerationDegree := family_generators CFSG.Sporadic.Model s

theorem sporadic_aut_card_le_pow (s : CFSG.Sporadic) [Finite s.Model] :
    Nat.card (s.Model ≃* s.Model) ≤ Nat.card s.Model ^ sporadicGenerationDegree :=
  family_aut_card_le_pow CFSG.Sporadic.Model s

end SymmetricSubgroupAsymptotics.CFSGGeneration
