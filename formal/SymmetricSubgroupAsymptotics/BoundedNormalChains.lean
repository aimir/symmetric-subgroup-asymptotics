import SymmetricSubgroupAsymptotics.MarkedC4SocleSurjectiveImage
import Mathlib.GroupTheory.Index

/-! Actual ambient-normal chains with bounded relative indices. Restriction
along an embedding and passage through a quotient can only decrease the
successive indices. Every actual minimal normal subgroup is detected at one
literal chain step. -/
set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.MarkedC4.OrdinaryNilpotentGeneration

structure BoundedNormalChain (B : ℕ) (G : Type) [Group G] where
  length : ℕ
  layer : ℕ → Subgroup G
  normal : ∀ i, (layer i).Normal
  first : layer 0 = ⊤
  last : layer length = ⊥
  decreasing : ∀ i, i < length → layer (i+1) ≤ layer i
  bound : ∀ i, i < length → (layer (i+1)).relIndex (layer i) ≤ B

namespace BoundedNormalChain
variable {B : ℕ} {G H : Type} [Group G] [Group H] [Finite G] [Finite H]

private theorem finite_relIndex_nonzero (A K : Subgroup G) : A.relIndex K ≠ 0 := by
  change Nat.card (K ⧸ A.subgroupOf K) ≠ 0
  exact Nat.ne_of_gt Nat.card_pos

private theorem comap_relIndex_le (A K : Subgroup G) (f : H →* G) :
    (A.comap f).relIndex (K.comap f) ≤ A.relIndex K := by
  rw [Subgroup.relIndex_comap]
  exact Subgroup.relIndex_le_of_le_right (Subgroup.map_comap_le f K)
    (finite_relIndex_nonzero A K)

private theorem map_relIndex_le (A K : Subgroup G) (f : G →* H) :
    (A.map f).relIndex (K.map f) ≤ A.relIndex K := by
  rw [← Subgroup.relIndex_comap, Subgroup.comap_map_eq]
  exact Subgroup.relIndex_le_of_le_left le_sup_left
    (finite_relIndex_nonzero A K)

/-- Pull back the same actual chain along a faithful embedding. -/
def ofInjective (D : BoundedNormalChain B G) (f : H →* G)
    (hf : Function.Injective f) : BoundedNormalChain B H where
  length := D.length
  layer i := (D.layer i).comap f
  normal i := by letI := D.normal i; infer_instance
  first := by rw [D.first, Subgroup.comap_top]
  last := by rw [D.last, MonoidHom.comap_bot, (MonoidHom.ker_eq_bot_iff f).mpr hf]
  decreasing i hi := Subgroup.comap_mono (D.decreasing i hi)
  bound i hi := (comap_relIndex_le _ _ f).trans (D.bound i hi)

/-- Map the same actual chain through an epimorphism. -/
def ofSurjective (D : BoundedNormalChain B G) (f : G →* H)
    (hf : Function.Surjective f) : BoundedNormalChain B H where
  length := D.length
  layer i := (D.layer i).map f
  normal i := (D.normal i).map f hf
  first := by
    rw [D.first]
    apply top_unique
    intro y _
    obtain ⟨x, rfl⟩ := hf y
    exact ⟨x, Subgroup.mem_top x, rfl⟩
  last := by rw [D.last, Subgroup.map_bot]
  decreasing i hi := Subgroup.map_mono (D.decreasing i hi)
  bound i hi := (map_relIndex_le _ _ f).trans (D.bound i hi)

/-- A minimal normal subgroup survives completely until a single bounded
step, where its intersection becomes trivial. Its order is paid there. -/
theorem minimalNormal_card_le (D : BoundedNormalChain B G)
    (E : Subgroup G) (hE : IsMinimalNormalSubgroup E) : Nat.card E ≤ B := by
  letI := hE.1
  letI (i : ℕ) : (D.layer i).Normal := D.normal i
  have hex : ∃ j, E ⊓ D.layer j = ⊥ := ⟨D.length, by rw [D.last, inf_bot_eq]⟩
  let j := Nat.find hex
  have hj : E ⊓ D.layer j = ⊥ := Nat.find_spec hex
  have hjlen : j ≤ D.length := Nat.find_min' hex (by rw [D.last, inf_bot_eq])
  have hjpos : 0 < j := by
    by_contra hz
    have hj0 : j = 0 := by omega
    rw [hj0, D.first, inf_top_eq] at hj
    exact hE.2.1 hj
  obtain ⟨i, hi⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hjpos)
  have hil : i < D.length := by omega
  have hprev : E ⊓ D.layer i ≠ ⊥ := Nat.find_min hex (by omega)
  have hwhole : E ⊓ D.layer i = E :=
    hE.2.2 _ inferInstance hprev inf_le_left
  have hle : E ≤ D.layer i := by rw [← hwhole]; exact inf_le_right
  have hzero : D.layer (i+1) ⊓ E = ⊥ := by
    rw [inf_comm]
    simpa only [hi, Nat.succ_eq_add_one] using hj
  have hcard : (D.layer (i+1)).relIndex E = Nat.card E := by
    rw [← Subgroup.inf_relIndex_right, hzero, Subgroup.relIndex_bot_left]
  calc
    Nat.card E = (D.layer (i+1)).relIndex E := hcard.symm
    _ ≤ (D.layer (i+1)).relIndex (D.layer i) :=
      Subgroup.relIndex_le_of_le_right hle (finite_relIndex_nonzero _ _)
    _ ≤ B := D.bound i hil

end BoundedNormalChain

/-- Every actual minimal normal section, in every actual subgroup and
quotient, has order bounded by B. Maps retain its original group. -/
def BoundedChiefSections (B : ℕ) (G : Type) [Group G] : Prop :=
  ∀ (H A : Type) [Group H] [Finite H] [Group A] [Finite A]
    (f : H →* G), Function.Injective f →
    ∀ (q : H →* A), Function.Surjective q →
    ∀ (E : Subgroup A), IsMinimalNormalSubgroup E → Nat.card E ≤ B

theorem BoundedNormalChain.chiefSections {B : ℕ} {G : Type} [Group G] [Finite G]
    (D : BoundedNormalChain B G) : BoundedChiefSections B G := by
  intro H A _ _ _ _ f hf q hq E hE
  exact ((D.ofInjective f hf).ofSurjective q hq).minimalNormal_card_le E hE

end SymmetricSubgroupAsymptotics.MarkedC4.OrdinaryNilpotentGeneration
