import SymmetricSubgroupAsymptotics.FullProjection

/-!
# Canonical lifts in a finite product of binary quotients

The quotient is formed from the actual coordinate homomorphisms. Every local
kernel is covered by the global kernel, and every original factor projection
is retained through a proved linear coordinate chart.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics

variable {ι : Type*} (D : ι → Type*) [∀ i, Group (D i)] (d : ι → ℕ)

/-- The product of the actual quotient maps, before a choice of basis. -/
def productBinaryQuotientNative
    (q : ∀ i, D i →* Multiplicative (Fin (d i) → ZMod 2)) :
    (∀ i, D i) →* Multiplicative (∀ i, Fin (d i) → ZMod 2) where
  toFun g := Multiplicative.ofAdd (fun i ↦ (q i (g i)).toAdd)
  map_one' := by apply Multiplicative.toAdd.injective; funext i; simp
  map_mul' g h := by
    apply Multiplicative.toAdd.injective
    funext i
    exact congrArg Multiplicative.toAdd ((q i).map_mul (g i) (h i))

/-- A quotient chart changes only binary coordinates, not the original maps. -/
def productBinaryQuotient {R : ℕ}
    (e : (Fin R → ZMod 2) ≃ₗ[ZMod 2] (∀ i, Fin (d i) → ZMod 2))
    (q : ∀ i, D i →* Multiplicative (Fin (d i) → ZMod 2)) :
    (∀ i, D i) →* Multiplicative (Fin R → ZMod 2) :=
  (AddMonoidHom.toMultiplicative e.symm.toLinearMap.toAddMonoidHom).comp
    (productBinaryQuotientNative D d q)

theorem productBinaryQuotient_surjective {R : ℕ}
    (e : (Fin R → ZMod 2) ≃ₗ[ZMod 2] (∀ i, Fin (d i) → ZMod 2))
    (q : ∀ i, D i →* Multiplicative (Fin (d i) → ZMod 2))
    (hq : ∀ i, Function.Surjective (q i)) :
    Function.Surjective (productBinaryQuotient D d e q) := by
  intro v
  choose g hg using (fun i ↦ hq i (Multiplicative.ofAdd (e v.toAdd i)))
  refine ⟨g, ?_⟩
  apply Multiplicative.toAdd.injective
  change e.symm (fun i ↦ (q i (g i)).toAdd) = v.toAdd
  simp only [hg]
  exact e.symm_apply_apply v.toAdd

/-- Literal occurrence projection in the quotient chart. -/
def productBinaryCoordinate {R : ℕ}
    (e : (Fin R → ZMod 2) ≃ₗ[ZMod 2] (∀ i, Fin (d i) → ZMod 2)) (i : ι) :
    (Fin R → ZMod 2) →ₗ[ZMod 2] (Fin (d i) → ZMod 2) :=
  (LinearMap.proj i).comp e.toLinearMap

theorem productBinaryCoordinate_surjective {R : ℕ}
    (e : (Fin R → ZMod 2) ≃ₗ[ZMod 2] (∀ i, Fin (d i) → ZMod 2)) (i : ι) :
    Function.Surjective (productBinaryCoordinate d e i) := by
  intro v
  refine ⟨e.symm (Pi.single i v), ?_⟩
  simp [productBinaryCoordinate]

theorem productBinaryQuotient_comm {R : ℕ}
    (e : (Fin R → ZMod 2) ≃ₗ[ZMod 2] (∀ i, Fin (d i) → ZMod 2))
    (q : ∀ i, D i →* Multiplicative (Fin (d i) → ZMod 2)) (i : ι) :
    (q i).comp (Pi.evalMonoidHom D i) =
      (AddMonoidHom.toMultiplicative (productBinaryCoordinate d e i).toAddMonoidHom).comp
        (productBinaryQuotient D d e q) := by
  apply MonoidHom.ext
  intro g
  apply Multiplicative.toAdd.injective
  change (q i (g i)).toAdd =
    e (e.symm (fun j ↦ (q j (g j)).toAdd)) i
  rw [e.apply_symm_apply]

theorem productBinaryQuotient_mem_ker {R : ℕ}
    (e : (Fin R → ZMod 2) ≃ₗ[ZMod 2] (∀ i, Fin (d i) → ZMod 2))
    (q : ∀ i, D i →* Multiplicative (Fin (d i) → ZMod 2)) (g : ∀ i, D i) :
    g ∈ (productBinaryQuotient D d e q).ker ↔ ∀ i, g i ∈ (q i).ker := by
  change Multiplicative.ofAdd (e.symm (fun i ↦ (q i (g i)).toAdd)) = 1 ↔ _
  constructor
  · intro h i
    have h' := congrArg (fun v : Multiplicative (Fin R → ZMod 2) ↦ e v.toAdd i) h
    change e (e.symm (fun j ↦ (q j (g j)).toAdd)) i = e 0 i at h'
    rw [e.apply_symm_apply, map_zero] at h'
    exact h'
  · intro h
    have hz : (fun i ↦ (q i (g i)).toAdd) = 0 := by
      funext i
      have hi : q i (g i) = 1 := h i
      simp [hi]
    rw [hz, map_zero]
    rfl

theorem productBinaryQuotient_kernel_coverage {R : ℕ}
    (e : (Fin R → ZMod 2) ≃ₗ[ZMod 2] (∀ i, Fin (d i) → ZMod 2))
    (q : ∀ i, D i →* Multiplicative (Fin (d i) → ZMod 2)) (i : ι) :
    (q i).ker ≤ (productBinaryQuotient D d e q).ker.map (Pi.evalMonoidHom D i) := by
  intro x hx
  apply Subgroup.mem_map.mpr
  refine ⟨Pi.mulSingle i x, ?_, by simp⟩
  rw [productBinaryQuotient_mem_ker]
  intro j
  by_cases hji : j = i
  · subst j; simpa using hx
  · simp [Pi.mulSingle_eq_of_ne hji]

/-- Uniform canonical full-coordinate error, for the actual finite product.
Every structural premise of the generic lift theorem is discharged here. -/
theorem productCanonical_full_projection_relative_error :
    ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, 1 ≤ N ∧ ∀ R ≥ N,
      ∀ {ι : Type*} [Fintype ι] (D : ι → Type*) [∀ i, Group (D i)] (d : ι → ℕ)
        (e : (Fin R → ZMod 2) ≃ₗ[ZMod 2] (∀ i, Fin (d i) → ZMod 2))
        (q : ∀ i, D i →* Multiplicative (Fin (d i) → ZMod 2)),
      (∀ i, Function.Surjective (q i)) → (∀ i, d i ≤ 4) → Fintype.card ι ≤ R →
      |(Nat.card {H : Subgroup (∀ i, D i) //
          (productBinaryQuotient D d e q).ker ≤ H ∧
            ∀ i, H.map (Pi.evalMonoidHom D i) = ⊤} : ℝ) /
        binarySubspaceCount R - 1| ≤ C * R * (2 : ℝ) ^ (-(R : ℝ) / 2) := by
  obtain ⟨C, hC, N, hN, hbound⟩ := canonicalLift_full_projection_relative_error
  refine ⟨C, hC, N, hN, ?_⟩
  intro R hR ι _ D _ d e q hq hd hι
  exact hbound R hR (productBinaryQuotient D d e q)
    (productBinaryQuotient_surjective D d e q hq) d D
    (Pi.evalMonoidHom D) q hq (productBinaryCoordinate d e)
    (productBinaryCoordinate_surjective d e) (productBinaryQuotient_comm D d e q)
    (productBinaryQuotient_kernel_coverage D d e q) hd hι

end SymmetricSubgroupAsymptotics
