import SymmetricSubgroupAsymptotics.SocleNormalGeneratorNumber
import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# Quotient socles from a uniform normal-generator bound

If every normal subgroup of a group has a normal-generating tuple of a
fixed width, the same holds in every surjective image. Apply this to the
preimage of a quotient's socle. The tuple statement requires no finiteness;
the numerical version uses the finite-group normal-generator invariant.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics

/-- A uniform bound on ambient normal-generating tuples descends along a
surjective homomorphism, by taking the preimage of the target subgroup. -/
theorem normal_generating_tuples_of_surjective
    {G H : Type} [Group G] [Group H] {t : ℕ}
    (f : G →* H) (hf : Function.Surjective f)
    (hgen : ∀ N : Subgroup G, N.Normal →
      ∃ x : Fin t → G, Subgroup.normalClosure (Set.range x) = N) :
    ∀ N : Subgroup H, N.Normal →
      ∃ x : Fin t → H, Subgroup.normalClosure (Set.range x) = N := by
  intro N hN
  obtain ⟨x, hx⟩ := hgen (N.comap f) (hN.comap f)
  let y : Fin t → H := fun i ↦ f (x i)
  refine ⟨y, ?_⟩
  have himage : f '' Set.range x = Set.range y := by
    ext z
    constructor
    · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
      exact ⟨i, rfl⟩
    · rintro ⟨i, rfl⟩
      exact ⟨x i, ⟨i, rfl⟩, rfl⟩
  calc
    Subgroup.normalClosure (Set.range y) =
        (Subgroup.normalClosure (Set.range x)).map f := by
      rw [Subgroup.map_normalClosure _ _ hf, himage]
    _ = (N.comap f).map f := congrArg (fun K : Subgroup G ↦ K.map f) hx
    _ = N := Subgroup.map_comap_eq_self_of_surjective hf N

/-- Every quotient socle inherits a uniform ambient normal-generator tuple
bound on normal subgroups of the original group. -/
theorem quotientSocleNormalGeneratorBound_of_normal_generating_tuples
    {G : Type} [Group G] {t : ℕ}
    (hgen : ∀ M : Subgroup G, M.Normal →
      ∃ x : Fin t → G, Subgroup.normalClosure (Set.range x) = M)
    (N : Subgroup G) [N.Normal] :
    SocleNormalGeneratorBound (G ⧸ N) t :=
  normal_generating_tuples_of_surjective (QuotientGroup.mk' N)
    (QuotientGroup.mk'_surjective N) hgen
    (finiteGroupSocle (G ⧸ N)) inferInstance

/-- Numerical input version, padded to exactly `t` generators. -/
theorem quotientSocleNormalGeneratorBound_of_normalGen_le
    {G : Type} [Group G] [Finite G] {t : ℕ}
    (hgen : ∀ M : Subgroup G, M.Normal → MarkedC4.normalGen M ≤ t)
    (N : Subgroup G) [N.Normal] :
    SocleNormalGeneratorBound (G ⧸ N) t := by
  apply quotientSocleNormalGeneratorBound_of_normal_generating_tuples _ N
  intro M hM
  letI := hM
  exact exists_normal_generating_tuple_of_normalGen_le M (hgen M hM)

/-- In particular, if every normal subgroup needs at most two ambient
normal generators, every quotient's socle also needs at most two. -/
theorem quotientSocle_normalGen_le_two_of_normalGen_le_two
    {G : Type} [Group G] [Finite G]
    (hgen : ∀ M : Subgroup G, M.Normal → MarkedC4.normalGen M ≤ 2)
    (N : Subgroup G) [N.Normal] :
    MarkedC4.normalGen (finiteGroupSocle (G ⧸ N)) ≤ 2 :=
  (socleNormalGeneratorBound_iff_normalGen_le (G ⧸ N) 2).mp
    (quotientSocleNormalGeneratorBound_of_normalGen_le hgen N)

end SymmetricSubgroupAsymptotics

end
