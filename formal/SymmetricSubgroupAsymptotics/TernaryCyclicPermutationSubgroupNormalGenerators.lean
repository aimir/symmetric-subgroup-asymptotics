import SymmetricSubgroupAsymptotics.TernaryMonomialOrbitUniform
import SymmetricSubgroupAsymptotics.LinearSemidirectSubgroupFullProjection
import SymmetricSubgroupAsymptotics.CoprimeCyclicQuotientSocles

/-! Actual subgroups of a ternary permutation semidirect product with
surjective cyclic block projection have two normal generators uniformly.
No pure complement or full translation subgroup is required. The separate
cardinality lemma records coprimality with two when the complement has odd
order, for subsequent binary affine-kernel applications. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.TernaryCyclicPermutationSubgroupNormalGenerators

open LinearSemidirectCoprimeSocleBounds LinearSemidirectSubgroupKernelChart

variable {R I : Type} [Group R] [Fintype I] [DecidableEq I]
  (b : R →* Equiv.Perm I)

def linearAction : R →* ((I → ZMod 3) ≃ₗ[ZMod 3] (I → ZMod 3)) :=
  TernaryMonomialCocycle.linearAction b (fun _ _ => 1)
    (fun _ => rfl) (by intros; simp)

abbrev Model := LinearSemidirectCoprimeSocleBounds.Model (linearAction b)

theorem uniform (g : R) (i₀ : I)
    (hcover : ∀ i : I, ∃ m : ℕ, ((b g)^m) i₀ = i) :
    UniformSubrepresentationGeneratorBound (linearRepresentation (linearAction b)) 1 := by
  apply TernaryMonomialOrbitUniform.uniform b (fun _ _ => 1)
    (fun _ => rfl) (by intros; simp) g (fun _ : Fin 1 => i₀)
  intro i
  obtain ⟨m,hm⟩ := hcover i
  exact ⟨0,m,hm⟩

variable [Finite R]

theorem normalGen_le [IsCyclic R] (K : Subgroup (Model b))
    (hsurj : Function.Surjective (projection (linearAction b) K))
    (g : R) (i₀ : I)
    (hcover : ∀ i : I, ∃ m : ℕ, ((b g)^m) i₀ = i)
    (N : Subgroup K) [N.Normal] : MarkedC4.normalGen N ≤ 2 := by
  apply LinearSemidirectSubgroupFullProjection.normalGen_le
    (linearAction b) K hsurj 1 1 (uniform b g i₀ hcover) ?_ N
  intro L hL
  letI := hL
  exact CoprimeCyclicQuotientSocles.normalGen_le_one_of_isCyclic L

theorem normal_generating_pairs [IsCyclic R] (K : Subgroup (Model b))
    (hsurj : Function.Surjective (projection (linearAction b) K))
    (g : R) (i₀ : I)
    (hcover : ∀ i : I, ∃ m : ℕ, ((b g)^m) i₀ = i)
    (N : Subgroup K) (hN : N.Normal) :
    ∃ x : Fin 2 → K, Subgroup.normalClosure (Set.range x) = N := by
  letI := hN
  exact exists_normal_generating_tuple_of_normalGen_le N
    (normalGen_le b K hsurj g i₀ hcover N)

theorem coprime_card (K : Subgroup (Model b))
    (hR : Nat.Coprime 2 (Nat.card R)) : Nat.Coprime 2 (Nat.card K) := by
  have hM : Nat.Coprime 2 (Nat.card (Model b)) := by
    rw [Nat.card_congr SemidirectProduct.equivProd,Nat.card_prod,
      Nat.card_congr Multiplicative.toAdd,Nat.card_fun,Nat.card_zmod]
    exact Nat.coprime_mul_iff_right.mpr
      ⟨(by decide : Nat.Coprime 2 3).pow_right _,hR⟩
  exact hM.of_dvd_right K.card_subgroup_dvd_card

end SymmetricSubgroupAsymptotics.TernaryCyclicPermutationSubgroupNormalGenerators

end
