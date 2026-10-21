import SymmetricSubgroupAsymptotics.FiniteSubgroupAdjunctionCoverage
import Mathlib.Tactic.Group

/-! A bounded left-coset cover reduces subgroup adjunction checks to its
literal representatives. The subgroup need not be normal. Local edges in
both generator directions prove coverage of the actual ambient group. -/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics

variable {G I : Type*} [Group G]

structure FiniteLeftCosetCover (generators : I → G) (H : Subgroup G) (q : ℕ) where
  representatives : Fin q → G
  identity : Fin q
  identity_mem : representatives identity ∈ H
  next : Fin q → I → Fin q
  step_mem : ∀ i j,
    representatives i * generators j * (representatives (next i j))⁻¹ ∈ H
  prev : Fin q → I → Fin q
  inverse_step_mem : ∀ i j,
    representatives i * (generators j)⁻¹ * (representatives (prev i j))⁻¹ ∈ H

namespace FiniteLeftCosetCover

variable {generators : I → G} {H : Subgroup G} {q : ℕ}
  (C : FiniteLeftCosetCover generators H q)

theorem covers (hgen : Subgroup.closure (Set.range generators) = ⊤) (g : G) :
    ∃ i : Fin q, g * (C.representatives i)⁻¹ ∈ H := by
  let S : Set G := {x | ∃ i : Fin q, x * (C.representatives i)⁻¹ ∈ H}
  have hOne : (1 : G) ∈ S :=
    ⟨C.identity, by simpa only [one_mul] using H.inv_mem C.identity_mem⟩
  let R : Subgroup G := {
    carrier := {a | (∀ x ∈ S, x * a ∈ S) ∧ (∀ x ∈ S, x * a⁻¹ ∈ S)}
    one_mem' := by constructor <;> intro x hx <;> simpa using hx
    mul_mem' := by
      intro a b ha hb
      constructor
      · intro x hx
        simpa only [mul_assoc] using hb.1 (x * a) (ha.1 x hx)
      · intro x hx
        simpa only [mul_inv_rev, mul_assoc] using ha.2 (x * b⁻¹) (hb.2 x hx)
    inv_mem' := by
      intro a ha
      exact ⟨ha.2, by simpa only [inv_inv] using ha.1⟩ }
  have hle : Subgroup.closure (Set.range generators) ≤ R := by
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨j, rfl⟩
    constructor
    · rintro x ⟨i, hi⟩
      refine ⟨C.next i j, ?_⟩
      have he := H.mul_mem hi (C.step_mem i j)
      convert he using 1; group
    · rintro x ⟨i, hi⟩
      refine ⟨C.prev i j, ?_⟩
      have he := H.mul_mem hi (C.inverse_step_mem i j)
      convert he using 1; group
  have hg : g ∈ R := hle (by rw [hgen]; exact Subgroup.mem_top g)
  simpa only [one_mul] using hg.1 1 hOne

theorem adjoin_eq_of_same_left_coset (x y : G) (hxy : x * y⁻¹ ∈ H) :
    H ⊔ Subgroup.closure {x} = H ⊔ Subgroup.closure {y} := by
  have hleft : x ∈ H ⊔ Subgroup.closure {y} := by
    have hh : x * y⁻¹ ∈ H ⊔ Subgroup.closure {y} :=
      (show H ≤ H ⊔ Subgroup.closure {y} from le_sup_left) hxy
    have hy : y ∈ H ⊔ Subgroup.closure {y} :=
      (show Subgroup.closure {y} ≤ H ⊔ Subgroup.closure {y} from le_sup_right)
        (Subgroup.subset_closure (by simp))
    simpa only [mul_assoc, inv_mul_cancel, mul_one] using
      (H ⊔ Subgroup.closure {y}).mul_mem hh hy
  have hright : y ∈ H ⊔ Subgroup.closure {x} := by
    have hh : (x * y⁻¹)⁻¹ ∈ H ⊔ Subgroup.closure {x} :=
      (show H ≤ H ⊔ Subgroup.closure {x} from le_sup_left) (H.inv_mem hxy)
    have hx : x ∈ H ⊔ Subgroup.closure {x} :=
      (show Subgroup.closure {x} ≤ H ⊔ Subgroup.closure {x} from le_sup_right)
        (Subgroup.subset_closure (by simp))
    simpa only [mul_inv_rev, inv_inv, mul_assoc, inv_mul_cancel, mul_one] using
      (H ⊔ Subgroup.closure {x}).mul_mem hh hx
  apply le_antisymm
  · apply sup_le le_sup_left
    apply (Subgroup.closure_le _).mpr
    intro z hz
    rcases Set.mem_singleton_iff.mp hz with rfl
    exact hleft
  · apply sup_le le_sup_left
    apply (Subgroup.closure_le _).mpr
    intro z hz
    rcases Set.mem_singleton_iff.mp hz with rfl
    exact hright

/-- Only the displayed coset representatives require adjunction witnesses. -/
theorem covered_adjoin {J : Type*} (rows : J → Subgroup G)
    (hgen : Subgroup.closure (Set.range generators) = ⊤)
    (hrep : ∀ i : Fin q, FiniteSubgroupAdjunctionCoverage.Covered rows
      (H ⊔ Subgroup.closure {C.representatives i})) (g : G) :
    FiniteSubgroupAdjunctionCoverage.Covered rows (H ⊔ Subgroup.closure {g}) := by
  obtain ⟨i, hi⟩ := C.covers hgen g
  rw [adjoin_eq_of_same_left_coset g (C.representatives i) hi]
  exact hrep i

end FiniteLeftCosetCover
end SymmetricSubgroupAsymptotics

end
