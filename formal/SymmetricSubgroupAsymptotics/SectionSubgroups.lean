import SymmetricSubgroupAsymptotics.CocycleLifts

/-!
# Actual section subgroups and homomorphic sections

A subgroup on which the original projection is bijective determines one
and only one homomorphic section, by the inverse restricted projection.
Conversely a section determines its literal range in the original group.
There is no quotient automorphism factor, chosen relabelling of the source,
or finiteness hypothesis. Both parameter spaces may be empty.
-/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics

variable {Q B : Type*} [Group Q] [Group B]

/-- Actual subgroups on which the original projection is bijective. -/
abbrev SectionSubgroup (π : Q →* B) :=
  {L : Subgroup Q // Function.Bijective (π.comp L.subtype)}

namespace SectionSubgroup

def restrictionEquiv (π : Q →* B) (L : SectionSubgroup π) : L.1 ≃* B :=
  MulEquiv.ofBijective (π.comp L.1.subtype) L.2

@[simp] theorem restrictionEquiv_apply (π : Q →* B) (L : SectionSubgroup π)
    (x : L.1) : restrictionEquiv π L x = π x.1 := rfl

/-- The section has values in precisely the original subgroup. -/
def toSection (π : Q →* B) (L : SectionSubgroup π) :
    HomomorphicLift π (MonoidHom.id B) :=
  ⟨L.1.subtype.comp (restrictionEquiv π L).symm.toMonoidHom, by
    apply MonoidHom.ext
    intro b
    exact (restrictionEquiv π L).apply_symm_apply b⟩

/-- No overcounting: the inverse construction is the actual range. -/
def ofSection (π : Q →* B) (s : HomomorphicLift π (MonoidHom.id B)) :
    SectionSubgroup π :=
  ⟨s.1.range, by
    constructor
    · rintro ⟨x, b, rfl⟩ ⟨y, c, rfl⟩ h
      apply Subtype.ext
      apply congrArg s.1
      change π (s.1 b) = π (s.1 c) at h
      simpa only [homomorphicLift_above, MonoidHom.id_apply] using h
    · intro b
      exact ⟨⟨s.1 b, ⟨b, rfl⟩⟩, homomorphicLift_above π (MonoidHom.id B) s b⟩⟩

@[simp] theorem ofSection_val (π : Q →* B)
    (s : HomomorphicLift π (MonoidHom.id B)) : (ofSection π s).1 = s.1.range := rfl

theorem section_range (π : Q →* B) (L : SectionSubgroup π) :
    (toSection π L).1.range = L.1 := by
  ext x
  constructor
  · rintro ⟨b, rfl⟩
    exact ((restrictionEquiv π L).symm b).property
  · intro hx
    refine ⟨restrictionEquiv π L ⟨x, hx⟩, ?_⟩
    exact congrArg Subtype.val ((restrictionEquiv π L).symm_apply_apply ⟨x, hx⟩)

@[simp] theorem ofSection_section (π : Q →* B) (L : SectionSubgroup π) :
    ofSection π (toSection π L) = L := Subtype.ext (section_range π L)

@[simp] theorem section_ofSection (π : Q →* B)
    (s : HomomorphicLift π (MonoidHom.id B)) : toSection π (ofSection π s) = s := by
  apply Subtype.ext
  apply MonoidHom.ext
  intro b
  change (((restrictionEquiv π (ofSection π s)).symm b : s.1.range) : Q) = s.1 b
  have he : (restrictionEquiv π (ofSection π s)).symm b =
      (⟨s.1 b, ⟨b, rfl⟩⟩ : s.1.range) := by
    apply (restrictionEquiv π (ofSection π s)).injective
    rw [MulEquiv.apply_symm_apply]
    exact (homomorphicLift_above π (MonoidHom.id B) s b).symm
  exact congrArg Subtype.val he

end SectionSubgroup

/-- Exact section-subgroup classification, with the original quotient
map and the identity of its original target retained. -/
def sectionSubgroupEquiv (π : Q →* B) :
    SectionSubgroup π ≃ HomomorphicLift π (MonoidHom.id B) where
  toFun := SectionSubgroup.toSection π
  invFun := SectionSubgroup.ofSection π
  left_inv := SectionSubgroup.ofSection_section π
  right_inv := SectionSubgroup.section_ofSection π

@[simp] theorem sectionSubgroupEquiv_symm_range (π : Q →* B)
    (s : HomomorphicLift π (MonoidHom.id B)) :
    ((sectionSubgroupEquiv π).symm s).1 = s.1.range := rfl

/-- A predicate on the actual original subgroup is retained by exact
range reconstruction, rather than replaced with a predicate on labels. -/
def sectionSubgroupRestrictedEquiv (π : Q →* B) (P : Subgroup Q → Prop) :
    {L : SectionSubgroup π // P L.1} ≃
      {s : HomomorphicLift π (MonoidHom.id B) // P s.1.range} :=
  (sectionSubgroupEquiv π).subtypeEquiv (fun L => by
    change P L.1 ↔ P (SectionSubgroup.toSection π L).1.range
    rw [SectionSubgroup.section_range])

/-- A direct exact cocycle equivalence as soon as one original section
exists. The action is induced by that actual section. -/
def sectionSubgroupCocycleEquiv (π : Q →* B)
    (s₀ : HomomorphicLift π (MonoidHom.id B)) :
    SectionSubgroup π ≃ KernelCocycle π s₀.1 :=
  (sectionSubgroupEquiv π).trans (homomorphicLiftEquivCocycle π (MonoidHom.id B) s₀)

theorem sectionSubgroup_card (π : Q →* B)
    (s₀ : HomomorphicLift π (MonoidHom.id B)) :
    Nat.card (SectionSubgroup π) = Nat.card (KernelCocycle π s₀.1) :=
  Nat.card_congr (sectionSubgroupCocycleEquiv π s₀)

end SymmetricSubgroupAsymptotics

end
