import SymmetricSubgroupAsymptotics.AbelianSemidirectDualClassIdentity

/-! The exact same-complement dual identity bounds an abelian semidirect
product by its actual dual stabilizers. Splitting off zero requires no
transitivity on nonzero functionals and no enlargement of the complement. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical BigOperators
namespace SymmetricSubgroupAsymptotics.AbelianSemidirectDualStabilizerClassBound
open AbelianSemidirectDualClassIdentity LinearContragredientSmallSpaceAction

variable {K N G : Type*} [Field K] [CommGroup N] [Group G]
    [Module K (Additive N)] [Finite K] [Finite N] [Finite G]

local instance : Finite (Module.Dual K (Additive N)) := Finite.of_injective
  (fun ℓ : Module.Dual K (Additive N) => (ℓ : Additive N → K)) DFunLike.coe_injective

local instance : Fintype (Module.Dual K (Additive N)) := Fintype.ofFinite _

theorem class_card_le_dual_stabilizer_sum
    (φ : G →* MulAut N) (ρ : G →* (Additive N ≃ₗ[K] Additive N))
    (hcompat : ∀ (g : G) (n : N), ρ g (Additive.ofMul n)=Additive.ofMul (φ g n)) :
    Nat.card (ConjClasses (N ⋊[φ] G)) ≤
      ∑ ℓ : Module.Dual K (Additive N), Nat.card (ConjClasses (dualStabilizer ρ ℓ)) := by
  have hh : Nat.card G*Nat.card (ConjClasses (N ⋊[φ] G)) ≤ Nat.card G*
      (∑ ℓ : Module.Dual K (Additive N), Nat.card (ConjClasses (dualStabilizer ρ ℓ))) := by
    calc
      _ = ∑ ℓ : Module.Dual K (Additive N),
          Nat.card (dualStabilizer ρ ℓ)*Nat.card (ConjClasses (dualStabilizer ρ ℓ)) :=
        class_weighted_identity φ ρ hcompat
      _ ≤ ∑ ℓ : Module.Dual K (Additive N),
          Nat.card G*Nat.card (ConjClasses (dualStabilizer ρ ℓ)) := by
        apply Finset.sum_le_sum
        intro ℓ _
        exact Nat.mul_le_mul_right _
          (Nat.card_le_card_of_injective (dualStabilizer ρ ℓ).subtype Subtype.val_injective)
      _ = _ := by rw [Finset.mul_sum]
  exact Nat.le_of_mul_le_mul_left hh (Nat.card_pos (α := G))

theorem class_card_le_add_punctured_bound
    (φ : G →* MulAut N) (ρ : G →* (Additive N ≃ₗ[K] Additive N))
    (hcompat : ∀ (g : G) (n : N), ρ g (Additive.ofMul n)=Additive.ofMul (φ g n))
    (c : ℕ) (hstab : ∀ ℓ : Module.Dual K (Additive N), ℓ≠0 →
      Nat.card (ConjClasses (dualStabilizer ρ ℓ)) ≤ c) :
    Nat.card (ConjClasses (N ⋊[φ] G)) ≤ Nat.card (ConjClasses G)+
      (Nat.card (Module.Dual K (Additive N))-1)*c := by
  have hz : dualStabilizer ρ 0=⊤ := by
    apply Subgroup.ext
    intro g
    change contragredient ρ g 0=0 ↔ True
    exact iff_of_true (map_zero _) trivial
  have hzero : Nat.card (ConjClasses (dualStabilizer ρ 0))=Nat.card (ConjClasses G) := by
    rw [hz]
    apply Nat.le_antisymm
    · exact Nat.card_le_card_of_surjective
        (ConjClasses.map (Subgroup.topEquiv : (⊤ : Subgroup G) ≃* G).symm.toMonoidHom)
        (ConjClasses.map_surjective Subgroup.topEquiv.symm.surjective)
    · exact Nat.card_le_card_of_surjective
        (ConjClasses.map (Subgroup.topEquiv : (⊤ : Subgroup G) ≃* G).toMonoidHom)
        (ConjClasses.map_surjective Subgroup.topEquiv.surjective)
  have hsum : (∑ ℓ ∈ (Finset.univ : Finset (Module.Dual K (Additive N))).erase 0,
      Nat.card (ConjClasses (dualStabilizer ρ ℓ))) ≤
      ((Finset.univ : Finset (Module.Dual K (Additive N))).erase 0).card*c := by
    calc
      _ ≤ ∑ _ℓ ∈ (Finset.univ : Finset (Module.Dual K (Additive N))).erase 0,c := by
        apply Finset.sum_le_sum
        intro ℓ hℓ
        exact hstab ℓ (Finset.mem_erase.mp hℓ).1
      _ = _ := by simp only [Finset.sum_const,nsmul_eq_mul,Nat.cast_id]
  calc
    _ ≤ ∑ ℓ : Module.Dual K (Additive N),
        Nat.card (ConjClasses (dualStabilizer ρ ℓ)) :=
      class_card_le_dual_stabilizer_sum φ ρ hcompat
    _ = (∑ ℓ ∈ (Finset.univ : Finset (Module.Dual K (Additive N))).erase 0,
        Nat.card (ConjClasses (dualStabilizer ρ ℓ)))+
          Nat.card (ConjClasses (dualStabilizer ρ 0)) :=
      (Finset.sum_erase_add _ _ (Finset.mem_univ (0 : Module.Dual K (Additive N)))).symm
    _ ≤ ((Finset.univ : Finset (Module.Dual K (Additive N))).erase 0).card*c+
        Nat.card (ConjClasses G) := Nat.add_le_add hsum hzero.le
    _ = _ := by simp only [Finset.card_erase_of_mem
        (Finset.mem_univ (0 : Module.Dual K (Additive N))),
        Finset.card_univ,←Nat.card_eq_fintype_card,add_comm]

end SymmetricSubgroupAsymptotics.AbelianSemidirectDualStabilizerClassBound
