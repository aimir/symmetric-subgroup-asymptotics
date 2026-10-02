import SymmetricSubgroupAsymptotics.NormalImageQuotient

/-!
# Normal sections under a surjective ambient map

The normal section between the inverse images of `A ≤ B` is canonically
isomorphic to the original section `B/A`.  Keeping this as a literal
normal-chain statement lets chief-series data be pulled back through a
quotient map without replacing its factors by abstract groups.
-/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics

variable {G H : Type} [Group G] [Group H]
variable (f : G →* H) (hf : Function.Surjective f)
variable (A B : Subgroup H) [A.Normal] [B.Normal]
variable (hAB : A ≤ B)

/-- Restriction of the ambient epimorphism to the inverse image of `B`,
followed by the literal quotient map `B → B/A`. -/
def normalChainComapMap : B.comap f →* normalChainQuotient A B :=
  (normalChainMap A B).comp
    { toFun := fun x => ⟨f x, x.property⟩
      map_one' := by ext; simp
      map_mul' := by intro x y; ext; simp }

include hf in
theorem normalChainComapMap_surjective :
    Function.Surjective (normalChainComapMap f A B) := by
  intro q
  obtain ⟨b, hb⟩ := normalChainMap_surjective A B q
  obtain ⟨g, hg⟩ := hf b
  let x : B.comap f := ⟨g, by simpa [hg] using b.property⟩
  refine ⟨x, ?_⟩
  simpa [normalChainComapMap, x, hg] using hb

include hAB in
theorem normalChainComapMap_kernel_image :
    (normalChainComapMap f A B).ker.map (B.comap f).subtype = A.comap f := by
  ext g
  constructor
  · rintro ⟨x, hx, rfl⟩
    change f x ∈ A
    change normalChainMap A B ⟨f x, x.property⟩ = 1 at hx
    exact (QuotientGroup.eq_one_iff (f x)).mp (congrArg Subtype.val hx)
  · intro hg
    have hB : g ∈ B.comap f := hAB hg
    let x : B.comap f := ⟨g, hB⟩
    refine ⟨x, ?_, rfl⟩
    change normalChainMap A B ⟨f g, hB⟩ = 1
    apply Subtype.ext
    exact (QuotientGroup.eq_one_iff (f g)).mpr hg

/-- The section between the two inverse images is the original section. -/
def normalChainQuotientComapSurjectiveEquiv :
    normalChainQuotient (A.comap f) (B.comap f) ≃*
      normalChainQuotient A B :=
  normalSectionQuotientEquiv (B.comap f) (A.comap f)
    (normalChainComapMap f A B)
    (normalChainComapMap_surjective f hf A B)
    (normalChainComapMap_kernel_image f A B hAB).symm

end SymmetricSubgroupAsymptotics

end
