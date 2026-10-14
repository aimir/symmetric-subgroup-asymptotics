import SymmetricSubgroupAsymptotics.ModuleWeightedCoordinateHeads
import SymmetricSubgroupAsymptotics.PermutationBinaryFourAugmentation

/-!
# The dimension cost of heads on four-point coordinates

The existing augmentation theorem forces every head of dimension two
to come from a three-dimensional subspace. Keeping that dimension cost
through the original coordinate filtration excludes a six-dimensional
head on a subspace of dimension at most eight in three four-point blocks.
No regular labels or invariant-subspace tables are required.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped MonoidAlgebra BigOperators

namespace SymmetricSubgroupAsymptotics

/-- Representation form of the dimension-sensitive coordinate filtration. -/
theorem representationHom_weighted_finrank_le_coordinates
    {k G V A : Type} [Field k] [Group G]
    [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    [AddCommGroup A] [Module k A] [FiniteDimensional k A]
    (weight n : ℕ) (W : Fin n → Type)
    [∀ i, AddCommGroup (W i)] [∀ i, Module k (W i)]
    (rho : Representation k G V) (tau : ∀ i, Representation k G (W i))
    (sigma : Representation k G A) (allowance : Fin n → ℕ)
    (hlocal : ∀ i (S : Subrepresentation (tau i)),
      weight * Module.finrank k (S.toRepresentation.IntertwiningMap sigma) ≤
        Module.finrank k S.toSubmodule + allowance i)
    (f : ∀ i, rho.IntertwiningMap (tau i))
    (hf : Function.Injective (fun v i ↦ f i v)) :
    weight * Module.finrank k (rho.IntertwiningMap sigma) ≤
      Module.finrank k V + ∑ i, allowance i := by
  let fi : ∀ i, rho.asModule →ₗ[k[G]] (tau i).asModule :=
    fun i ↦ Representation.IntertwiningMap.equivLinearMapAsModule rho (tau i) (f i)
  have hi : Function.Injective (fun v i ↦ fi i v) := hf
  have hmodule : ∀ i (S : Submodule k[G] (tau i).asModule),
      weight * Module.finrank k (S →ₗ[k[G]] sigma.asModule) ≤
        Module.finrank k S + allowance i := by
    intro i S
    have h := hlocal i (Subrepresentation.ofSubmodule' S)
    rw [(Representation.IntertwiningMap.equivLinearMapAsModule _ sigma).finrank_eq] at h
    let e := submoduleRepresentationModuleEquiv (tau i) S
    have hhom := (moduleHomDomainEquiv (k := k) (A := sigma.asModule) e).finrank_eq
    have hdim := (e.restrictScalars k).finrank_eq
    have htag := (Subrepresentation.ofSubmodule' S).toRepresentation.asModuleEquiv.finrank_eq
    rw [hhom, hdim, htag]
    exact h
  rw [(Representation.IntertwiningMap.equivLinearMapAsModule rho sigma).finrank_eq]
  have h := moduleHom_weighted_finrank_le_coordinate_bounds
    (k := k) (R := k[G]) (A := sigma.asModule) weight n
    (fun i ↦ (tau i).asModule) allowance hmodule rho.asModule fi hi
  simpa only [rho.asModuleEquiv.finrank_eq] using h

/-- The sharp four-point head bound also records the dimension required
to attain two. This is valid for every transitive binary-group action. -/
theorem twoGroup_fourPoint_subrepresentationHead_weighted
    {G X : Type} [Group G] [Finite G] [MulAction G X]
    [Finite X] [MulAction.IsPretransitive G X]
    (hG : IsPGroup 2 G) (x : X) (hcard : Nat.card X = 4)
    (S : Subrepresentation (permutationFunctionRepresentation (ZMod 2) G X)) :
    3 * Module.finrank (ZMod 2)
        (S.toRepresentation.IntertwiningMap
          (Representation.trivial (ZMod 2) G (ZMod 2))) ≤
      Module.finrank (ZMod 2) S.toSubmodule + 3 := by
  have hhead := twoGroup_permutationSubrepresentationHead_le_width hG 2
    (by simpa using hcard) x S
  norm_num at hhead
  by_cases htwo : 2 ≤ Module.finrank (ZMod 2)
      (S.toRepresentation.IntertwiningMap
        (Representation.trivial (ZMod 2) G (ZMod 2)))
  · have hdim := PermutationBinaryFourAugmentation.dimension_eq_three_of_head_ge_two
      S x hcard htwo
    omega
  · omega

/-- The strict-dimensional case for a module embedded in three actual
transitive four-point binary permutation coordinates. -/
theorem twoGroup_threeFourPoint_head_le_five_of_dimension_le_eight
    {G V : Type} [Group G] [Finite G]
    [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (hG : IsPGroup 2 G) (X : Fin 3 → Type)
    [∀ i, Finite (X i)] [∀ i, MulAction G (X i)]
    [∀ i, MulAction.IsPretransitive G (X i)]
    (x : ∀ i, X i) (hcard : ∀ i, Nat.card (X i) = 4)
    (rho : Representation (ZMod 2) G V)
    (f : ∀ i, rho.IntertwiningMap
      (permutationFunctionRepresentation (ZMod 2) G (X i)))
    (hf : Function.Injective (fun v i ↦ f i v))
    (hdim : Module.finrank (ZMod 2) V ≤ 8) :
    Module.finrank (ZMod 2)
      (rho.IntertwiningMap (Representation.trivial (ZMod 2) G (ZMod 2))) ≤ 5 := by
  have h := representationHom_weighted_finrank_le_coordinates 3 3
    (fun i ↦ X i → ZMod 2) rho
    (fun i ↦ permutationFunctionRepresentation (ZMod 2) G (X i))
    (Representation.trivial (ZMod 2) G (ZMod 2)) (fun _ ↦ 3)
    (fun i S ↦ twoGroup_fourPoint_subrepresentationHead_weighted hG (x i) (hcard i) S)
    f hf
  have hsum : (∑ _i : Fin 3, (3 : ℕ)) = 9 := by simp
  rw [hsum] at h
  omega

end SymmetricSubgroupAsymptotics

end
