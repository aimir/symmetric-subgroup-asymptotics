import SymmetricSubgroupAsymptotics.RepresentationCoordinateHeads
import Mathlib.RepresentationTheory.Coinduced
import Mathlib.RepresentationTheory.Maschke
import Mathlib.RepresentationTheory.Irreducible

/-! Every scalar character of an actual central subgroup occurs on an
irreducible constituent of a nonzero coinduced representation. This
constructs the target representations needed by the character owner. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped MonoidAlgebra
namespace SymmetricSubgroupAsymptotics
variable {k G : Type} [Field k] [Group G]

def scalarCharacterRepresentation {H : Type} [Group H] (χ : H→*k) :
    Representation k H k where
  toFun h := χ h • LinearMap.id
  map_one' := by ext; simp
  map_mul' g h := by ext; simp [mul_comm]

def scalarCharacterSupported (H : Subgroup G) (χ : H→*k) :
    Representation.coindV H.subtype (scalarCharacterRepresentation χ) := by
  classical
  refine ⟨fun g=>if hg:g∈H then χ ⟨g,hg⟩ else 0,?_⟩
  intro h g
  change (if hg':(h:G)*g∈H then χ ⟨(h:G)*g,hg'⟩ else 0)=
    scalarCharacterRepresentation χ h (if hg':g∈H then χ ⟨g,hg'⟩ else 0)
  by_cases hg:g∈H
  · have hhg : (h:G)*g∈H := H.mul_mem h.property hg
    rw [dif_pos hhg,dif_pos hg]
    change χ (h*⟨g,hg⟩)=χ h*χ ⟨g,hg⟩
    exact χ.map_mul _ _
  · have hhg : (h:G)*g∉H := by
      intro h'
      exact hg ((H.mul_mem_cancel_left h.property).mp h')
    rw [dif_neg hhg,dif_neg hg]
    exact (map_zero _).symm

@[simp] theorem scalarCharacterSupported_one (H : Subgroup G) (χ : H→*k) :
    (scalarCharacterSupported H χ).val 1=1 := by
  classical
  change (if hg:(1:G)∈H then χ ⟨1,hg⟩ else 0)=1
  rw [dif_pos H.one_mem]
  exact χ.map_one

theorem coinduced_central_scalar (H : Subgroup G) (hH : H≤Subgroup.center G)
    (χ : H→*k) (h : H)
    (v : Representation.coindV H.subtype (scalarCharacterRepresentation χ)) :
    Representation.coind H.subtype (scalarCharacterRepresentation χ) (h:G) v=χ h • v := by
  apply Subtype.ext
  funext g
  change v.val (g*(h:G))=χ h*v.val g
  rw [Subgroup.mem_center_iff.mp (hH h.property) g]
  exact v.property h g

/-- A finite-dimensional original constituent with the prescribed
central scalar action. No faithful-tuple or counting claim is assumed. -/
theorem exists_irreducible_central_character [Finite G] [NeZero (Nat.card G:k)]
    (H : Subgroup G) (hH : H≤Subgroup.center G) (χ : H→*k) :
    ∃ (W : Type) (_ : AddCommGroup W) (_ : Module k W)
      (_ : FiniteDimensional k W) (ρ : Representation k G W),
      Representation.IsIrreducible ρ ∧ ∀ (h : H) (v : W),ρ (h:G) v=χ h • v := by
  classical
  letI : Fintype G := Fintype.ofFinite G
  let ψ : Representation k G (Representation.coindV H.subtype
      (scalarCharacterRepresentation χ)) :=
    Representation.coind H.subtype (scalarCharacterRepresentation χ)
  letI : Nontrivial (Representation.coindV H.subtype (scalarCharacterRepresentation χ)) := by
    refine ⟨⟨scalarCharacterSupported H χ,0,?_⟩⟩
    intro he
    have hz := congrArg (fun v:Representation.coindV H.subtype
      (scalarCharacterRepresentation χ)=>v.val 1) he
    change (scalarCharacterSupported H χ).val 1=0 at hz
    rw [scalarCharacterSupported_one] at hz
    exact one_ne_zero hz
  letI : Nontrivial ψ.asModule := ψ.asModuleEquiv.toEquiv.nontrivial
  letI : AddCommGroup ψ.asModule := inferInstance
  obtain ⟨S,hS⟩ := IsSemisimpleModule.exists_simple_submodule k[G] ψ.asModule
  let τ : Representation k G (Subrepresentation.ofSubmodule' S).toSubmodule :=
    (Subrepresentation.ofSubmodule' S).toRepresentation
  letI : IsSimpleModule k[G] S := hS
  letI : AddCommGroup ((Subrepresentation.ofSubmodule' S).toSubmodule) := inferInstance
  letI : AddCommGroup τ.asModule := inferInstance
  have hs : IsSimpleModule k[G] τ.asModule :=
    (submoduleRepresentationModuleEquiv ψ S).toLinearMap.isSimpleModule_iff_of_bijective
      (submoduleRepresentationModuleEquiv ψ S).bijective |>.mp hS
  refine ⟨(Subrepresentation.ofSubmodule' S).toSubmodule,inferInstance,inferInstance,
    inferInstance,τ,(Representation.irreducible_iff_isSimpleModule_asModule τ).mpr hs,?_⟩
  intro h v
  apply Subtype.ext
  exact coinduced_central_scalar H hH χ h v.val

end SymmetricSubgroupAsymptotics
