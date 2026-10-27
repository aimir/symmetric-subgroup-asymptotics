/-
Copyright (c) AxiomMath contributors. All rights reserved.
SPDX-License-Identifier: Apache-2.0
-/
import SymmetricSubgroupAsymptotics.CFSGYSectionGeneration

/-!
The literal definitions below are an isolated minimal-import port of
CFSG/Open/MonsterY443Defs.lean at AxiomMath/CFSG
69cb972f587a3ecc035e092253167ff2e303c962 (lines40–68).
The namespace and dependency imports are changed; the4.35 module/public/
expose annotations are omitted. The literal defining bodies are retained.
The generation
proof is new and uses the already checked connected-involution theorem.

This raw DERIVED Y443 carrier is not the original Y555 node-centralizer
derived carrier. No equivalence between those carriers is asserted here.
No source simplicity, finiteness, order or named-group recognition premise.
-/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGAxiomMonsterY443ElevenGenerators

def monsterY443ArmLength : Fin 3 → ℕ
  | 0 => 4
  | 1 => 4
  | 2 => 3

abbrev MonsterY443Gen : Type := Option (Σ i : Fin 3,Fin (monsterY443ArmLength i))

def MonsterY443Adj : MonsterY443Gen → MonsterY443Gen → Prop
  | none,none => False
  | none,some ⟨_,j⟩ => j.val=0
  | some ⟨_,j⟩,none => j.val=0
  | some ⟨i,j⟩,some ⟨i',j'⟩ =>
    i=i' ∧ (j.val+1=j'.val ∨ j'.val+1=j.val)

def monsterY443Node (i : Fin 3) (j : ℕ) (hj : j<monsterY443ArmLength i) :
    FreeGroup MonsterY443Gen := FreeGroup.of (some ⟨i,⟨j,hj⟩⟩)

def monsterY443SpiderWord : FreeGroup MonsterY443Gen :=
  FreeGroup.of none*monsterY443Node 0 0 (by decide)*monsterY443Node 0 1 (by decide)*
  FreeGroup.of none*monsterY443Node 1 0 (by decide)*monsterY443Node 1 1 (by decide)*
  FreeGroup.of none*monsterY443Node 2 0 (by decide)*monsterY443Node 2 1 (by decide)

def monsterY443Rels : Set (FreeGroup MonsterY443Gen) :=
  {w | ∃ s,w=FreeGroup.of s^2} ∪
  {w | ∃ s t,MonsterY443Adj s t ∧ w=(FreeGroup.of s*FreeGroup.of t)^3} ∪
  {w | ∃ s t,s≠t ∧ ¬MonsterY443Adj s t ∧ w=(FreeGroup.of s*FreeGroup.of t)^2} ∪
  {monsterY443SpiderWord^10}

abbrev MonsterY443 : Type := PresentedGroup monsterY443Rels
abbrev MonsterY443Derived : Subgroup MonsterY443 := commutator MonsterY443

private def arms : CFSG.Models.YGroups.Arms :=
  ⟨monsterY443ArmLength,by intro i; fin_cases i <;> decide⟩

theorem generator_square (i : MonsterY443Gen) :
    (PresentedGroup.of (rels := monsterY443Rels) i)^2=1 := by
  have h := PresentedGroup.one_of_mem (rels := monsterY443Rels)
    (x := FreeGroup.of i^2) (Or.inl (Or.inl (Or.inl ⟨i,rfl⟩)))
  simpa only [map_pow,PresentedGroup.of] using h

theorem adjacent_product_cube (i j : MonsterY443Gen) (hij : MonsterY443Adj i j) :
    (PresentedGroup.of (rels := monsterY443Rels) i*PresentedGroup.of j)^3=1 := by
  have h := PresentedGroup.one_of_mem (rels := monsterY443Rels)
    (x := (FreeGroup.of i*FreeGroup.of j)^3)
    (Or.inl (Or.inl (Or.inr ⟨i,j,hij,rfl⟩)))
  simpa only [map_pow,map_mul,PresentedGroup.of] using h

theorem connected (i : MonsterY443Gen) :
    Relation.ReflTransGen MonsterY443Adj none i := by
  have hrel : CFSG.Models.YGroups.Adjacent arms=MonsterY443Adj := by
    funext s t
    apply propext
    cases s with
    | none => cases t <;> rfl
    | some s =>
      rcases s with ⟨a,j⟩
      cases t with
      | none => rfl
      | some t =>
        rcases t with ⟨b,k⟩
        rfl
  rw [←hrel]
  exact CFSGGeneration.y_connected arms i

theorem derived_generators :
    ∃ S : Finset MonsterY443Derived,
      Subgroup.closure (S : Set MonsterY443Derived)=⊤ ∧ S.card≤11 := by
  have hcard : Nat.card MonsterY443Gen-1=11 := by
    change Nat.card (Option ((i : Fin 3)×Fin (arms.length i)))-1=11
    rw [Nat.card_eq_fintype_card,Fintype.card_option,Fintype.card_sigma]
    simp only [Fintype.card_fin]
    decide +kernel
  have h := CFSGGeneration.connected_involution_derived_generators
    (PresentedGroup.of (rels := monsterY443Rels)) none
    (PresentedGroup.closure_range_of monsterY443Rels)
    generator_square MonsterY443Adj adjacent_product_cube connected
  simpa only [hcard] using h

end SymmetricSubgroupAsymptotics.CFSGAxiomMonsterY443ElevenGenerators
