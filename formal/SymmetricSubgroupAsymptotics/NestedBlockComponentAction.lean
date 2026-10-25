import SymmetricSubgroupAsymptotics.SurjectiveEquivariantActionFactor
import SymmetricSubgroupAsymptotics.ImprimitiveBlockEvaluation

/-! The actual component of a composite block map acts on the inner
blocks. Surjectivity of the inner point map proves the required kernel
containment before descending through the literal stabilizer image. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.NestedBlockComponentAction

variable {A Ω X Y : Type} [Group A]
    [MulAction A Ω] [MulAction A X] [MulAction A Y]
    (b : Ω → X) (hb : ∀ (g : A) (ω : Ω), b (g • ω) = g • b ω)
    (c : X → Y) (hc : ∀ (g : A) (x : X), c (g • x) = g • c x)

include hb hc in
theorem composite_equivariant (g : A) (ω : Ω) :
    (c ∘ b) (g • ω) = g • (c ∘ b) ω := by
  change c (b (g • ω)) = g • c (b ω)
  rw [hb,hc]

abbrev Source (y : Y) := MulAction.stabilizer A y
abbrev OuterFibre (y : Y) := originalBlockFibre (c ∘ b) y
abbrev InnerFibre (y : Y) := originalBlockFibre c y
abbrev Component (y : Y) :=
  originalBlockComponent (c ∘ b) (composite_equivariant b hb c hc) y

def innerMap (y : Y) : OuterFibre b c y → InnerFibre c y :=
  fun u => ⟨b u.val,u.property⟩

theorem innerMap_surjective (hbs : Function.Surjective b) (y : Y) :
    Function.Surjective (innerMap b c y) := by
  intro x
  obtain ⟨ω,hω⟩ := hbs x.val
  refine ⟨⟨ω,?_⟩,?_⟩
  · change c (b ω) = y
    rw [hω]
    exact x.property
  · exact Subtype.ext hω

abbrev sourceOuterAction (y : Y) : MulAction (Source (A := A) y) (OuterFibre b c y) :=
  MulAction.compHom _ (originalBlockFibreAction (c ∘ b) (composite_equivariant b hb c hc) y)

abbrev sourceInnerAction (y : Y) : MulAction (Source (A := A) y) (InnerFibre c y) :=
  MulAction.compHom _ (originalBlockFibreAction c hc y)

theorem source_equivariant (y : Y) :
    letI := sourceOuterAction b hb c hc y
    letI := sourceInnerAction c hc y
    ∀ (g : Source (A := A) y) (u : OuterFibre b c y),
      innerMap b c y (g • u) = g • innerMap b c y u := by
  letI := sourceOuterAction b hb c hc y
  letI := sourceInnerAction c hc y
  intro g u
  apply Subtype.ext
  change b (g.val • u.val) = g.val • b u.val
  exact hb g.val u.val

def projection (y : Y) : Source (A := A) y →* Component b hb c hc y :=
  (originalBlockFibreAction (c ∘ b) (composite_equivariant b hb c hc) y).rangeRestrict

theorem projection_surjective (y : Y) : Function.Surjective (projection b hb c hc y) :=
  MonoidHom.rangeRestrict_surjective _

def innerHom (hbs : Function.Surjective b) (y : Y) :
    Component b hb c hc y →* Equiv.Perm (InnerFibre c y) := by
  letI := sourceOuterAction b hb c hc y
  letI := sourceInnerAction c hc y
  exact SurjectiveEquivariantActionFactor.hom (projection b hb c hc y)
    (projection_surjective b hb c hc y) (innerMap b c y) (innerMap_surjective b c hbs y)
    (source_equivariant b hb c hc y) (fun _ _ => rfl)

theorem innerHom_projection (hbs : Function.Surjective b) (y : Y)
    (g : Source (A := A) y) :
    innerHom b hb c hc hbs y (projection b hb c hc y g) = originalBlockFibreAction c hc y g := by
  letI := sourceOuterAction b hb c hc y
  letI := sourceInnerAction c hc y
  apply Equiv.ext
  intro x
  exact congrArg (fun f : Equiv.Perm (InnerFibre c y) => f x)
    (SurjectiveEquivariantActionFactor.hom_apply (projection b hb c hc y)
      (projection_surjective b hb c hc y) (innerMap b c y) (innerMap_surjective b c hbs y)
      (source_equivariant b hb c hc y) (fun _ _ => rfl) g)

theorem innerHom_range (hbs : Function.Surjective b) (y : Y) :
    (innerHom b hb c hc hbs y).range = originalBlockComponent c hc y := by
  ext σ
  constructor
  · rintro ⟨h,he⟩
    obtain ⟨g,rfl⟩ := projection_surjective b hb c hc y h
    exact ⟨g,(innerHom_projection b hb c hc hbs y g).symm.trans he⟩
  · rintro ⟨g,he⟩
    exact ⟨projection b hb c hc y g,(innerHom_projection b hb c hc hbs y g).trans he⟩

abbrev componentAction (hbs : Function.Surjective b) (y : Y) :
    MulAction (Component b hb c hc y) (InnerFibre c y) :=
  MulAction.compHom _ (innerHom b hb c hc hbs y)

theorem innerMap_equivariant (hbs : Function.Surjective b) (y : Y) :
    letI := componentAction b hb c hc hbs y
    ∀ (g : Component b hb c hc y) (u : OuterFibre b c y),
      innerMap b c y (g • u) = g • innerMap b c y u := by
  letI := sourceOuterAction b hb c hc y
  letI := sourceInnerAction c hc y
  exact SurjectiveEquivariantActionFactor.equivariant (projection b hb c hc y)
    (projection_surjective b hb c hc y) (innerMap b c y) (innerMap_surjective b c hbs y)
    (source_equivariant b hb c hc y) (fun _ _ => rfl)

def innerFibreEquiv (y : Y) (x : InnerFibre c y) :
    originalBlockFibre (innerMap b c y) x ≃ originalBlockFibre b x.val where
  toFun u := ⟨u.val.val,congrArg Subtype.val u.property⟩
  invFun u := ⟨⟨u.val,by
    change c (b u.val) = y
    rw [u.property]
    exact x.property⟩,Subtype.ext u.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

end SymmetricSubgroupAsymptotics.NestedBlockComponentAction
