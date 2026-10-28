import SymmetricSubgroupAsymptotics.CFSGAxiomMonsterY443ElevenGenerators
import SymmetricSubgroupAsymptotics.CFSGClassificationTransport

/-! INTERNAL dispatcher interface for the direct Axiom69 backend. This file
does NOT construct Classification, change the old Index.Model, or add an
input to any public endpoint. Its classifier field is a target to be proved
from the actual upstream classification and genuine non-M carrier bridges.
The new Monster branch is the actual raw-derived Y443 carrier. The historical
Y555-centralizer Monster is explicitly excluded from the old-index branch.
-/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGCatalogueWithAxiomMonster
open CFSGAxiomMonsterY443ElevenGenerators CFSGReduction

abbrev OldIndex := {i : CFSG.Index // i≠CFSG.Index.sporadic .monster}
abbrev Index := Sum OldIndex Unit

def Model : Index → Type
  | .inl i => i.val.Model
  | .inr _ => MonsterY443Derived

instance (i : Index) : Group (Model i) := by
  cases i with
  | inl i => change Group i.val.Model; infer_instance
  | inr _ => change Group MonsterY443Derived; infer_instance

structure ModelWitness (G : Type) [Group G] where
  index : Index
  equiv : G≃*Model index

/-- Unproved INTERNAL bridge target. Every actual isomorphism in this field
must come from the completed upstream classifier and checked carrier maps. -/
structure Classification : Prop where
  classify : ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G],
    Nonempty (ModelWitness G)

def modelWitness (hclass : Classification)
    (G : Type) [Group G] [Finite G] [IsSimpleGroup G] : ModelWitness G :=
  Classical.choice (hclass.classify G)

theorem finite_model {G : Type} [Group G] [Finite G] (W : ModelWitness G) :
    Finite (Model W.index) := Finite.of_equiv G W.equiv.toEquiv

theorem simple_model {G : Type} [Group G] [IsSimpleGroup G] (W : ModelWitness G) :
    IsSimpleGroup (Model W.index) := W.equiv.symm.isSimpleGroup

theorem noncommutative_model {G : Type} [Group G] (W : ModelWitness G)
    (hn : ¬IsMulCommutative G) : ¬IsMulCommutative (Model W.index) :=
  fun hc => hn ((isMulCommutative_congr W.equiv).mpr hc)

/-- Generic dispatch preserves the SAME source and literal actual isomorphism.
The model-property arguments here are proof-construction branches, not new
fields of the classification target or a public quantitative callback. -/
theorem of_nonabelian_simple_models (hclass : Classification)
    (P : (G : Type) → [Group G] → Prop)
    (transport : ∀ {G H : Type} [Group G] [Group H],(G≃*H) → P H → P G)
    (old : ∀ (i : CFSG.Index),i≠CFSG.Index.sporadic .monster →
      ∀ [Finite i.Model] [IsSimpleGroup i.Model],¬IsMulCommutative i.Model → P i.Model)
    (raw : ∀ [Finite MonsterY443Derived] [IsSimpleGroup MonsterY443Derived],
      ¬IsMulCommutative MonsterY443Derived → P MonsterY443Derived)
    (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (hn : ¬IsMulCommutative G) :
    P G := by
  obtain ⟨i,e⟩ := modelWitness hclass G
  cases i with
  | inl i =>
    let e0 : G≃*i.val.Model := e
    letI : Finite i.val.Model := Finite.of_equiv G e0.toEquiv
    letI : IsSimpleGroup i.val.Model := e0.symm.isSimpleGroup
    have hc : ¬IsMulCommutative i.val.Model :=
      fun hh => hn ((isMulCommutative_congr e0).mpr hh)
    exact transport e0 (old i.val i.property hc)
  | inr u =>
    let e0 : G≃*MonsterY443Derived := e
    letI : Finite MonsterY443Derived := Finite.of_equiv G e0.toEquiv
    letI : IsSimpleGroup MonsterY443Derived := e0.symm.isSimpleGroup
    have hc : ¬IsMulCommutative MonsterY443Derived :=
      fun hh => hn ((isMulCommutative_congr e0).mpr hh)
    exact transport e0 (raw hc)

end SymmetricSubgroupAsymptotics.CFSGCatalogueWithAxiomMonster
