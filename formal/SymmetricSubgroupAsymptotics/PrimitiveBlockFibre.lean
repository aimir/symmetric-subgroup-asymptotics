import SymmetricSubgroupAsymptotics.TransitiveBlockQuotient
import SymmetricSubgroupAsymptotics.ImprimitiveBlockEvaluation

/-! A cover of the original point stabilizer makes the literal action on
the original block fibre primitive. Its faithful permutation image is the
same `originalBlockComponent` used in the actual-chief recurrence. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics

variable {A Ω X : Type} [Group A] [MulAction A Ω] [MulAction A X]
variable (b : Ω → X) (hb : ∀ (a : A) (ω : Ω), b (a • ω) = a • b ω) (x₀ : X)

abbrev originalBlockStabilizerMulAction :
    MulAction (MulAction.stabilizer A x₀) (originalBlockFibre b x₀) :=
  MulAction.compHom _ (originalBlockFibreAction b hb x₀)

/-- The same original stabilizer acts transitively on each actual fibre
of an equivariant map from a transitive action. -/
theorem originalBlockStabilizer_pretransitive [MulAction.IsPretransitive A Ω] :
    letI := originalBlockStabilizerMulAction b hb x₀
    MulAction.IsPretransitive (MulAction.stabilizer A x₀) (originalBlockFibre b x₀) := by
  letI := originalBlockStabilizerMulAction b hb x₀
  constructor
  intro u v
  obtain ⟨a, ha⟩ := MulAction.exists_smul_eq A u.1 v.1
  have hx : a ∈ MulAction.stabilizer A x₀ := by
    change a • x₀ = x₀
    calc
      a • x₀ = a • b u.1 := congrArg (fun x => a • x) u.2.symm
      _ = b (a • u.1) := (hb a u.1).symm
      _ = b v.1 := congrArg b ha
      _ = x₀ := v.2
  refine ⟨⟨a, hx⟩, ?_⟩
  apply Subtype.ext
  exact ha

theorem originalBlockStabilizer_preprimitive [MulAction.IsPretransitive A Ω]
    (ω₀ : Ω) (hω : b ω₀ = x₀)
    (hc : MulAction.stabilizer A ω₀ ⋖ MulAction.stabilizer A x₀) :
    letI := originalBlockStabilizerMulAction b hb x₀
    MulAction.IsPreprimitive (MulAction.stabilizer A x₀) (originalBlockFibre b x₀) := by
  let H := MulAction.stabilizer A x₀
  let F := originalBlockFibre b x₀
  letI := originalBlockStabilizerMulAction b hb x₀
  letI : MulAction.IsPretransitive H F := originalBlockStabilizer_pretransitive b hb x₀
  let z : F := ⟨ω₀, hω⟩
  have hz : MulAction.stabilizer H z = (MulAction.stabilizer A ω₀).subgroupOf H := by
    ext a
    change a • z = z ↔ (a : A) • ω₀ = ω₀
    constructor
    · intro he
      exact congrArg Subtype.val he
    · intro he
      apply Subtype.ext
      exact he
  have hm : IsCoatom ((MulAction.stabilizer A ω₀).subgroupOf H) := by
    have hi : IsCoatom (⟨MulAction.stabilizer A ω₀, hc.le⟩ : Set.Iic H) :=
      Set.Iic.isCoatom_iff.mpr hc
    let e : Subgroup H ≃o Set.Iic H := Subgroup.MapSubtype.orderIso H
    exact (e.symm.isCoatom_iff _).mpr hi
  letI : Nontrivial F := by
    obtain ⟨a, haH, haS⟩ := SetLike.exists_of_lt hc.lt
    refine ⟨⟨(⟨a, haH⟩ : H) • z, z, ?_⟩⟩
    intro he
    apply haS
    exact congrArg Subtype.val he
  apply (MulAction.isCoatom_stabilizer_iff_preprimitive H z).mp
  rwa [hz]

/-- Passing to the actual permutation range preserves the primitive
action on precisely the same original fibre. -/
theorem originalBlockComponent_preprimitive [MulAction.IsPretransitive A Ω]
    (ω₀ : Ω) (hω : b ω₀ = x₀)
    (hc : MulAction.stabilizer A ω₀ ⋖ MulAction.stabilizer A x₀) :
    MulAction.IsPreprimitive (originalBlockComponent b hb x₀) (originalBlockFibre b x₀) := by
  let H := MulAction.stabilizer A x₀
  let F := originalBlockFibre b x₀
  letI := originalBlockStabilizerMulAction b hb x₀
  letI : MulAction.IsPreprimitive H F :=
    originalBlockStabilizer_preprimitive b hb x₀ ω₀ hω hc
  let f : MulActionHom (fun h : H => (originalBlockFibreAction b hb x₀).rangeRestrict h)
      F F := {
    toFun := id
    map_smul' := fun _ _ => rfl }
  exact MulAction.IsPreprimitive.of_surjective (f := f) Function.surjective_id

end SymmetricSubgroupAsymptotics
