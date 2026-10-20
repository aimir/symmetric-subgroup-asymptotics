import SymmetricSubgroupAsymptotics.DualGeneratorSchurCapacity
import SymmetricSubgroupAsymptotics.SchurTargetExtension
import SymmetricSubgroupAsymptotics.SchurMultiplicityInjectiveTarget

/-!
# Integral Schur bounds along actual exact maps

The simple type is fixed while its multiplicities in the actual kernel
and target are added. Injective and equivariant transport likewise retain
the original action. These lemmas require bounds on the displayed modules,
not on abstract composition factors with unrelated actions.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped MonoidAlgebra

namespace SymmetricSubgroupAsymptotics

local instance finiteDimensionalExactSubmodule
    {k R A : Type} [Field k] [Ring R] [Algebra k R]
    [AddCommGroup A] [Module R A] [Module k A] [IsScalarTower k R A]
    [FiniteDimensional k A] (S : Submodule R A) : FiniteDimensional k S :=
  FiniteDimensional.of_injective
    (S.subtype.restrictScalars k) S.subtype_injective

theorem representationSchurCapacity_le_of_simple_multiplicity
    {k G V : Type} [Field k] [Group G]
    [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (rho : Representation k G V) (n : ℕ)
    (h : ∀ S : Submodule k[G] rho.asModule, [IsSimpleModule k[G] S] →
      schurSocleMultiplicity (k := k) (R := k[G]) (A := rho.asModule) (X := S) ≤
        n * Module.finrank (Module.End k[G] S) S) :
    representationSchurCapacity rho ≤ n := by
  unfold representationSchurCapacity schurCapacity
  apply csSup_le (Set.insert_nonempty _ _)
  rintro x (rfl | ⟨S, hS, rfl⟩)
  · positivity
  · letI : IsSimpleModule k[G] S := hS
    letI : Nontrivial S := IsSimpleModule.nontrivial k[G] S
    rw [schurSimpleRatio_eq_multiplicity_division
      (k := k) (R := k[G]) (A := rho.asModule) (X := S)]
    have hepos : 0 < Module.finrank (Module.End k[G] S) S := by
      have hspos : 0 < Module.finrank k S := Module.finrank_pos (R := k) (M := S)
      have htower := schur_simple_finrank_tower (k := k) (R := k[G]) (X := S)
      by_contra he
      have hz : Module.finrank (Module.End k[G] S) S = 0 :=
        Nat.eq_zero_of_not_pos he
      rw [htower, hz, mul_zero] at hspos
      omega
    have heposR : (0 : ℝ) < Module.finrank (Module.End k[G] S) S := by
      exact_mod_cast hepos
    apply (div_le_iff₀ heposR).mpr
    exact_mod_cast h S

theorem representationSchurCapacity_le_of_injective
    {k G V W : Type} [Field k] [Group G]
    [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    [AddCommGroup W] [Module k W] [FiniteDimensional k W]
    (rho : Representation k G V) (tau : Representation k G W)
    (f : rho.IntertwiningMap tau) (hf : Function.Injective f)
    (n : ℕ) (htau : representationSchurCapacity tau ≤ n) :
    representationSchurCapacity rho ≤ n := by
  apply representationSchurCapacity_le_of_simple_multiplicity rho n
  intro S _hS
  let fM := Representation.IntertwiningMap.equivLinearMapAsModule rho tau f
  exact (schurSocleMultiplicity_le_of_injective_target
    (k := k) (R := k[G]) (X := S) fM hf).trans
      (schurSocleMultiplicity_le_nat_mul_end_finrank_of_capacity_le tau n htau)

theorem representationSchurCapacity_le_of_equiv
    {k G V W : Type} [Field k] [Group G]
    [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    [AddCommGroup W] [Module k W] [FiniteDimensional k W]
    (rho : Representation k G V) (tau : Representation k G W)
    (e : rho.Equiv tau) (n : ℕ)
    (htau : representationSchurCapacity tau ≤ n) :
    representationSchurCapacity rho ≤ n :=
  representationSchurCapacity_le_of_injective rho tau e.toIntertwiningMap
    e.injective n htau

theorem representationSchurCapacity_le_kernel_add_target
    {k G V W : Type} [Field k] [Group G]
    [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    [AddCommGroup W] [Module k W] [FiniteDimensional k W]
    (rho : Representation k G V) (tau : Representation k G W)
    (q : rho.IntertwiningMap tau) (hq : Function.Surjective q)
    (a b : ℕ)
    (hker : representationSchurCapacity q.ker.toRepresentation ≤ a)
    (htarget : representationSchurCapacity tau ≤ b) :
    representationSchurCapacity rho ≤ (a + b : ℕ) := by
  apply representationSchurCapacity_le_of_simple_multiplicity rho (a + b)
  intro S _hS
  have hk := schurSocleMultiplicity_le_nat_mul_end_finrank_of_capacity_le
    q.ker.toRepresentation a hker (X := S)
  have he := schurSocleMultiplicity_eq_of_target_linearEquiv
    (k := k) (R := k[G]) (X := S)
    (submoduleRepresentationModuleEquiv rho q.ker.asSubmodule).symm
  rw [he] at hk
  have ht := schurSocleMultiplicity_le_nat_mul_end_finrank_of_capacity_le
    tau b htarget (X := S)
  have hsplit := representationSchurMultiplicity_le_kernel_add_target rho tau q hq (X := S)
  exact hsplit.trans (by simpa only [Nat.add_mul] using Nat.add_le_add hk ht)

end SymmetricSubgroupAsymptotics

end
