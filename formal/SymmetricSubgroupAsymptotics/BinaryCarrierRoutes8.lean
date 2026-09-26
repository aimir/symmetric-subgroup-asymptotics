import SymmetricSubgroupAsymptotics.BinaryMenuCayley8T26
import SymmetricSubgroupAsymptotics.BinaryCarrierEpimorphism8T27To28
import SymmetricSubgroupAsymptotics.BinaryCarrierEpimorphism8T35To18
import SymmetricSubgroupAsymptotics.BinaryCarrierEpimorphism8T35To29
import SymmetricSubgroupAsymptotics.BinaryCarrierEpimorphism8T35To31

/-! The seven fixed degree-eight carrier routes, on the original literal
permutation subgroups. Three routes are identities; the other four use the
checked original-generator epimorphisms. Every source and target action
has its original eight points. No action conjugacy, normalizer equality,
profile weight or complete-normal-registry result is asserted here. -/
set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics.BinaryCarrierRoutes8

inductive Master
  | x
  | j
  | p
  deriving DecidableEq, Fintype

inductive Target
  | t18
  | t26
  | t27
  | t28
  | t29
  | t31
  | t35
  deriving DecidableEq, Fintype

/-- All groups below keep the exact original ordered generator tuple. -/
def masterArity : Master → ℕ
  | .x => 3
  | .j => 2
  | .p => 3

def masterGenerators : (m : Master) → Fin (masterArity m) → Equiv.Perm (Fin 8)
  | .x => BinaryMenuCayley8T26.generators
  | .j => BinaryMenuCayley8T27.generators
  | .p => BinaryMenuCayley8T35.generators

def targetArity : Target → ℕ
  | .t18 => 5
  | .t26 => 3
  | .t27 => 2
  | .t28 => 3
  | .t29 => 5
  | .t31 => 3
  | .t35 => 3

def targetGenerators : (t : Target) → Fin (targetArity t) → Equiv.Perm (Fin 8)
  | .t18 => BinaryMenuCayley8T18.generators
  | .t26 => BinaryMenuCayley8T26.generators
  | .t27 => BinaryMenuCayley8T27.generators
  | .t28 => BinaryMenuCayley8T28.generators
  | .t29 => BinaryMenuCayley8T29.generators
  | .t31 => BinaryMenuCayley8T31.generators
  | .t35 => BinaryMenuCayley8T35.generators

def sourceMaster : Target → Master
  | .t18 => .p
  | .t26 => .x
  | .t27 => .j
  | .t28 => .j
  | .t29 => .p
  | .t31 => .p
  | .t35 => .p

def masterSubgroup (m : Master) : Subgroup (Equiv.Perm (Fin 8)) :=
  Subgroup.closure (Set.range (masterGenerators m))

def originalSubgroup (t : Target) : Subgroup (Equiv.Perm (Fin 8)) :=
  Subgroup.closure (Set.range (targetGenerators t))

abbrev Source (t : Target) := masterSubgroup (sourceMaster t)
abbrev Original (t : Target) := originalSubgroup t

abbrev sourcePoints (_m : Master) := Fin 8
abbrev originalPoints (_t : Target) := Fin 8

/-- Both actions are the faithful literal inclusions on their original points.
The epimorphism is not asserted to intertwine these permutation actions. -/
def sourceAction (t : Target) : Source t →* Equiv.Perm (sourcePoints (sourceMaster t)) :=
  (masterSubgroup (sourceMaster t)).subtype

def originalAction (t : Target) : Original t →* Equiv.Perm (originalPoints t) :=
  (originalSubgroup t).subtype

theorem physical_degree (t : Target) :
    Nat.card (sourcePoints (sourceMaster t)) = 8 ∧ Nat.card (originalPoints t) = 8 := by
  constructor <;> simp

/-- The fixed map for each literal original carrier color. -/
def hom : (t : Target) → Source t →* Original t
  | .t18 => BinaryCarrierEpimorphism8T35To18.hom
  | .t26 => MonoidHom.id _
  | .t27 => MonoidHom.id _
  | .t28 => BinaryCarrierEpimorphism8T27To28.hom
  | .t29 => BinaryCarrierEpimorphism8T35To29.hom
  | .t31 => BinaryCarrierEpimorphism8T35To31.hom
  | .t35 => MonoidHom.id _

theorem hom_surjective (t : Target) : Function.Surjective (hom t) := by
  cases t with
  | t18 => exact BinaryCarrierEpimorphism8T35To18.hom_surjective
  | t26 => intro x; exact ⟨x, rfl⟩
  | t27 => intro x; exact ⟨x, rfl⟩
  | t28 => exact BinaryCarrierEpimorphism8T27To28.hom_surjective
  | t29 => exact BinaryCarrierEpimorphism8T35To29.hom_surjective
  | t31 => exact BinaryCarrierEpimorphism8T35To31.hom_surjective
  | t35 => intro x; exact ⟨x, rfl⟩

def sourceGenerator (t : Target) (j : Fin (masterArity (sourceMaster t))) : Source t :=
  ⟨masterGenerators (sourceMaster t) j, Subgroup.subset_closure (Set.mem_range_self j)⟩

/-- Complete source images in the original source-tuple order. -/
def generatorImages : (t : Target) →
    Fin (masterArity (sourceMaster t)) → Equiv.Perm (Fin 8)
  | .t18 => BinaryCarrierEpimorphism8T35To18.images
  | .t26 => BinaryMenuCayley8T26.generators
  | .t27 => BinaryMenuCayley8T27.generators
  | .t28 => BinaryCarrierEpimorphism8T27To28.images
  | .t29 => BinaryCarrierEpimorphism8T35To29.images
  | .t31 => BinaryCarrierEpimorphism8T35To31.images
  | .t35 => BinaryMenuCayley8T35.generators

theorem hom_generator (t : Target) (j : Fin (masterArity (sourceMaster t))) :
    ((hom t (sourceGenerator t j) : Original t) : Equiv.Perm (Fin 8)) =
      generatorImages t j := by
  cases t with
  | t18 => exact BinaryCarrierEpimorphism8T35To18.hom_generator j
  | t26 => rfl
  | t27 => rfl
  | t28 => exact BinaryCarrierEpimorphism8T27To28.hom_generator j
  | t29 => exact BinaryCarrierEpimorphism8T35To29.hom_generator j
  | t31 => exact BinaryCarrierEpimorphism8T35To31.hom_generator j
  | t35 => rfl

/-- A separate literal epimorphism for every original occurrence, including
repeated colors. This is the input to coordinatewise full inverse images. -/
def coordinateHom {ι : Type*} (targets : ι → Target) :
    ∀ i, Source (targets i) →* Original (targets i) := fun i => hom (targets i)

theorem coordinateHom_surjective {ι : Type*} (targets : ι → Target) :
    ∀ i, Function.Surjective (coordinateHom targets i) := fun i => hom_surjective (targets i)

end SymmetricSubgroupAsymptotics.BinaryCarrierRoutes8
