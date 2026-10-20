import SymmetricSubgroupAsymptotics.BoundedProductNormalChain
import SymmetricSubgroupAsymptotics.MarkedC4BoundedOrbitImages

/-! Hereditary chief-section bounds retain actual embeddings and quotient
maps. Their original bounded-orbit instance is constructed from the actual
orbit-image product, independently of the number of original orbits. -/
set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.MarkedC4.OrdinaryNilpotentGeneration
namespace BoundedChiefSections

variable {B : ℕ} {G Q : Type} [Group G] [Finite G] [Group Q] [Finite Q]

theorem minimalNormal_card_le (h : BoundedChiefSections B G)
    (E : Subgroup G) (hE : IsMinimalNormalSubgroup E) : Nat.card E ≤ B :=
  h G G (MonoidHom.id G) Function.injective_id
    (MonoidHom.id G) Function.surjective_id E hE

omit [Finite G] [Finite Q] in
/-- Restriction keeps the literal original subgroup embedding. -/
theorem of_injective (h : BoundedChiefSections B G) (j : Q →* G)
    (hj : Function.Injective j) : BoundedChiefSections B Q := by
  intro H A _ _ _ _ f hf q hq E hE
  exact h H A (j.comp f) (hj.comp hf) q hq E hE

omit [Finite Q] in
/-- A subgroup of a quotient is lifted by the actual fibre product, whose
left projection is faithful and right projection is onto. -/
theorem of_surjective (h : BoundedChiefSections B G) (f : G →* Q)
    (hf : Function.Surjective f) : BoundedChiefSections B Q := by
  intro H A _ _ _ _ j hj q hq E hE
  let P : Subgroup (G × H) := {
    carrier := {z | f z.1 = j z.2}
    one_mem' := by change f 1 = j 1; simp only [map_one]
    mul_mem' := by
      intro a b ha hb
      change f (a.1*b.1) = j (a.2*b.2)
      rw [map_mul, map_mul, ha, hb]
    inv_mem' := by
      intro a ha
      change f a.1⁻¹ = j a.2⁻¹
      rw [map_inv, map_inv, ha] }
  let left : P →* G := {
    toFun z := z.val.1
    map_one' := rfl
    map_mul' _ _ := rfl }
  let right : P →* H := {
    toFun z := z.val.2
    map_one' := rfl
    map_mul' _ _ := rfl }
  have hleft : Function.Injective left := by
    intro a b hab
    apply Subtype.ext
    apply Prod.ext hab
    apply hj
    exact a.property.symm.trans ((congrArg f hab).trans b.property)
  have hright : Function.Surjective right := by
    intro z
    obtain ⟨g, hg⟩ := hf (j z)
    exact ⟨⟨(g,z), hg⟩, rfl⟩
  exact h P A left hleft (q.comp right) (hq.comp hright) E hE

end BoundedChiefSections

/-- Every chief section of an actual bounded-orbit source has order at
most C!, including all its subgroups and quotients. -/
theorem boundedChiefSections_of_orbitCutoff {C b : ℕ}
    (G : Subgroup (PermutationGroup b))
    (hG : OrbitCutoffFamilies.OrbitCutoff C G) :
    BoundedChiefSections C.factorial G :=
  boundedChiefSections_of_faithful_product (fun x => ↥(BoundedOrbitImages.Image G x))
    (BoundedOrbitImages.subdirect G) (BoundedOrbitImages.subdirect_injective G)
    (BoundedOrbitImages.image_card_le_factorial G hG)

end SymmetricSubgroupAsymptotics.MarkedC4.OrdinaryNilpotentGeneration
