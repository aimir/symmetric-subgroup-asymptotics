import SymmetricSubgroupAsymptotics.ModuleCoordinateHeads

/-!
# Dimension-sensitive coordinate bounds for heads

Coordinate filtration preserves inequalities of the form
`weight * dim Hom(S,A) ≤ dim S + allowance`. Unlike an unweighted head
bound, this records the dimension required to attain equality. The
three-coordinate, weight-three consequence isolates the rank-six case
in the regular Klein-four argument for the twelve-point C₃ core.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace SymmetricSubgroupAsymptotics

universe u
variable {k R A : Type u} [Field k] [Ring R] [Algebra k R]
  [AddCommGroup A] [Module R A] [Module k A] [IsScalarTower k R A]

/-- A jointly injective family of coordinate maps preserves a weighted
head bound, with only the actual source dimension charged once. -/
theorem moduleHom_weighted_finrank_le_coordinate_bounds
    [FiniteDimensional k A] (weight n : ℕ)
    (V : Fin n → Type u) [∀ i, AddCommGroup (V i)] [∀ i, Module R (V i)]
    [∀ i, Module k (V i)] [∀ i, IsScalarTower k R (V i)]
    (allowance : Fin n → ℕ)
    (hlocal : ∀ i (S : Submodule R (V i)),
      weight * Module.finrank k (S →ₗ[R] A) ≤ Module.finrank k S + allowance i)
    (M : Type u) [AddCommGroup M] [Module R M] [Module k M]
    [IsScalarTower k R M] [FiniteDimensional k M]
    (f : ∀ i, M →ₗ[R] V i) (hf : Function.Injective (fun m i ↦ f i m)) :
    weight * Module.finrank k (M →ₗ[R] A) ≤
      Module.finrank k M + ∑ i, allowance i := by
  induction n generalizing M with
  | zero =>
      letI : Subsingleton M := ⟨fun x y ↦ hf (funext (fun i ↦ Fin.elim0 i))⟩
      letI : Subsingleton (M →ₗ[R] A) := ⟨fun f g ↦ by
        ext x
        rw [Subsingleton.elim x 0, map_zero, map_zero]⟩
      simp [Module.finrank_zero_of_subsingleton]
  | succ n ih =>
      let K := LinearMap.ker (f 0)
      letI : FiniteDimensional k K := FiniteDimensional.of_injective
        (K.subtype.restrictScalars k) K.subtype_injective
      letI : FiniteDimensional k (M ⧸ K) := FiniteDimensional.of_surjective
        (K.mkQ.restrictScalars k) K.mkQ_surjective
      let tail : ∀ i : Fin n, K →ₗ[R] V i.succ :=
        fun i ↦ (f i.succ).comp K.subtype
      have htail : Function.Injective (fun m i ↦ tail i m) := by
        intro x y h
        apply Subtype.ext
        apply hf
        funext i
        refine Fin.cases ?_ (fun j ↦ ?_) i
        · exact x.property.trans y.property.symm
        · exact congrFun h j
      have hrec := ih (fun i : Fin n ↦ V i.succ)
        (fun i ↦ allowance i.succ) (fun i ↦ hlocal i.succ) K tail htail
      have hfirst := hlocal 0 (LinearMap.range (f 0))
      have hquot := (moduleHomDomainEquiv (k := k) (A := A)
        (f 0).quotKerEquivRange).finrank_eq
      have hsplit := schurHom_finrank_le_submodule_quotient (k := k) (A := A) K
      change Module.finrank k ((M ⧸ K) →ₗ[R] A) = _ at hquot
      rw [hquot] at hsplit
      have hdimQuot : Module.finrank k (M ⧸ K) =
          Module.finrank k (LinearMap.range (f 0)) :=
        ((f 0).quotKerEquivRange.restrictScalars k).finrank_eq
      have hdim : Module.finrank k (M ⧸ K) + Module.finrank k K =
          Module.finrank k M :=
        (K.restrictScalars k).finrank_quotient_add_finrank
      rw [Fin.sum_univ_succ]
      calc
        weight * Module.finrank k (M →ₗ[R] A) ≤
            weight * (Module.finrank k (K →ₗ[R] A) +
              Module.finrank k (LinearMap.range (f 0) →ₗ[R] A)) :=
          Nat.mul_le_mul_left weight hsplit
        _ = weight * Module.finrank k (K →ₗ[R] A) +
            weight * Module.finrank k (LinearMap.range (f 0) →ₗ[R] A) := by
          rw [Nat.mul_add]
        _ ≤ (Module.finrank k K + ∑ i : Fin n, allowance i.succ) +
            (Module.finrank k (LinearMap.range (f 0)) + allowance 0) :=
          Nat.add_le_add hrec hfirst
        _ = Module.finrank k M + (allowance 0 +
            ∑ i : Fin n, allowance i.succ) := by omega

/-- Three local inequalities `3 * head ≤ dimension + 3` exclude a
six-dimensional head as soon as the original submodule has dimension
at most eight. This is the strict case in the three regular-V₄ blocks. -/
theorem moduleHom_finrank_le_five_of_three_weighted_coordinates
    [FiniteDimensional k A]
    (V : Fin 3 → Type u) [∀ i, AddCommGroup (V i)] [∀ i, Module R (V i)]
    [∀ i, Module k (V i)] [∀ i, IsScalarTower k R (V i)]
    (hlocal : ∀ i (S : Submodule R (V i)),
      3 * Module.finrank k (S →ₗ[R] A) ≤ Module.finrank k S + 3)
    (M : Type u) [AddCommGroup M] [Module R M] [Module k M]
    [IsScalarTower k R M] [FiniteDimensional k M]
    (f : ∀ i, M →ₗ[R] V i) (hf : Function.Injective (fun m i ↦ f i m))
    (hdim : Module.finrank k M ≤ 8) :
    Module.finrank k (M →ₗ[R] A) ≤ 5 := by
  have h := moduleHom_weighted_finrank_le_coordinate_bounds
    (k := k) (R := R) (A := A) 3 3 V (fun _ ↦ 3) hlocal M f hf
  have hsum : (∑ _i : Fin 3, (3 : ℕ)) = 9 := by simp
  rw [hsum] at h
  omega

end SymmetricSubgroupAsymptotics

end
