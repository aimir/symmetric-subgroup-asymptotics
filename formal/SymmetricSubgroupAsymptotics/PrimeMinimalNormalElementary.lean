import SymmetricSubgroupAsymptotics.AbelianMinimalNormal
import SymmetricSubgroupAsymptotics.ZmudFaithfulCharacterInput
import Mathlib.GroupTheory.PGroup

/-!
# Prime-primary minimal normal subgroups are elementary

A finite minimal normal `p`-subgroup is elementary abelian.  The proof is
kept in the ambient group: the intrinsic center is characteristic and hence
its image is ambient-normal; minimality and the nontrivial-center theorem
make it the whole subgroup.  The abelian prime-torsion dichotomy then gives
exponent `p`.

This small structural lemma is the group-to-module entry point for the
noncentral binary socle in the fixed-frame argument.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical IsMulCommutative

namespace SymmetricSubgroupAsymptotics

variable (p : ℕ) [Fact p.Prime]
variable {G : Type} [Group G] [Finite G]

/-- A finite minimal normal prime subgroup is commutative. -/
theorem minimalNormal_isMulCommutative_of_isPGroup
    (M : Subgroup G) (hM : IsMinimalNormalSubgroup M)
    (hp : IsPGroup p M) : IsMulCommutative M := by
  letI : M.Normal := hM.1
  letI : Nontrivial M := M.nontrivial_iff_ne_bot.mpr hM.2.1
  let Z : Subgroup G := (Subgroup.center M).map M.subtype
  letI : Z.Normal := by
    dsimp only [Z]
    infer_instance
  have hZne : Z ≠ ⊥ := by
    letI : Nontrivial (Subgroup.center M) := IsPGroup.center_nontrivial hp
    rw [Subgroup.ne_bot_iff_exists_ne_one]
    obtain ⟨z, hz⟩ := exists_ne (1 : Subgroup.center M)
    refine ⟨⟨(z.1.1 : G), ⟨z.1, z.2, rfl⟩⟩, ?_⟩
    intro hz1
    have hu : (z.1.1 : G) = 1 :=
      congrArg (fun q : Z => (q.1 : G)) hz1
    apply hz
    apply Subtype.ext
    apply Subtype.ext
    exact hu
  have hZle : Z ≤ M := Subgroup.map_subtype_le (Subgroup.center M)
  have hZM : Z = M := hM.2.2 Z inferInstance hZne hZle
  exact IsMulCommutative.of_comm fun x y ↦ by
    have hxZ : (x.1 : G) ∈ Z := by
      rw [hZM]
      exact x.2
    obtain ⟨z, hz, hzx⟩ := hxZ
    have hcomm : Commute z y := (Subgroup.mem_center_iff.mp hz y).symm
    apply Subtype.ext
    change x.1 * y.1 = y.1 * x.1
    rw [← hzx]
    exact congrArg Subtype.val hcomm.eq

/-- The same subgroup has exponent exactly dividing `p`; no abstract
classification of finite abelian groups is used. -/
theorem minimalNormal_pow_prime_eq_one_of_isPGroup
    (M : Subgroup G) (hM : IsMinimalNormalSubgroup M)
    (hp : IsPGroup p M) : ∀ x : M, x ^ p = 1 := by
  letI : M.Normal := hM.1
  letI : IsMulCommutative M :=
    minimalNormal_isMulCommutative_of_isPGroup p M hM hp
  have hmin : ∀ K : Subgroup G, K.Normal → K ≤ M → K = ⊥ ∨ K = M := by
    intro K hKnormal hKM
    by_cases hK : K = ⊥
    · exact Or.inl hK
    · exact Or.inr (hM.2.2 K hKnormal hK hKM)
  rcases abelian_minimal_normal_prime_dichotomy M p hmin with hexp | hcop
  · exact hexp
  · exfalso
    letI : Nontrivial M := M.nontrivial_iff_ne_bot.mpr hM.2.1
    obtain ⟨n, hn, hcard⟩ := hp.nontrivial_iff_card.mp inferInstance
    have hpdvd : p ∣ Nat.card M := by
      rw [hcard]
      exact dvd_pow_self p (ne_of_gt hn)
    exact (Fact.out : p.Prime).coprime_iff_not_dvd.mp hcop.symm hpdvd

end SymmetricSubgroupAsymptotics

end
