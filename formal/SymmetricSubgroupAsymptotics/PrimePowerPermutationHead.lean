import SymmetricSubgroupAsymptotics.PermutationSubrepresentationHead
import SymmetricSubgroupAsymptotics.SylowPrimePowerTransitive

/-! In prime-power permutation degree, a Sylow subgroup is transitive.
One of its semiregular elements bounds the head under the entire original
group. This gives the coarse half-degree bound needed for binary pair
kernels without a transitive-subgroup catalogue or a generator hypothesis. -/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics

variable {k G X : Type} [Field k] [Group G] [Finite G]
  [Finite X] [Nontrivial X] [MulAction G X] [MulAction.IsPretransitive G X]

theorem primePower_permutationSubrepresentationHead_le_div
    {p a : ℕ} [Fact p.Prime] (hcard : Nat.card X = p ^ a)
    (M : Subrepresentation (permutationFunctionRepresentation k G X)) :
    Module.finrank k
      (M.toRepresentation.IntertwiningMap (Representation.trivial k G k)) ≤
        Nat.card X / p := by
  classical
  letI : Fintype X := Fintype.ofFinite X
  let P : Sylow p G := Classical.choice inferInstance
  letI : MulAction.IsPretransitive P X :=
    sylow_isPretransitive_of_card_eq_prime_pow P hcard
  obtain ⟨g, _, _, _, hcount⟩ :=
    pGroup_exists_semiregular_element (X := X) P.isPGroup'
  have hfixed := permutation_elementFixedSpace_le_cyclicOrbitCount
    (k := k) (X := X) g
  have hsource := subrepresentationHead_le_ambient_elementFixedSpace
    (permutationFunctionRepresentation k G X) M (g : G)
  change Module.finrank k
      (M.toRepresentation.IntertwiningMap (Representation.trivial k G k)) ≤
    Module.finrank k
      (representationElementFixedSpace (permutationFunctionRepresentation k P X) g)
    at hsource
  exact hsource.trans (hfixed.trans_eq hcount)

theorem binaryEight_permutationSubrepresentationHead_le_four
    (hcard : Nat.card X = 8)
    (M : Subrepresentation (permutationFunctionRepresentation (ZMod 2) G X)) :
    Module.finrank (ZMod 2)
      (M.toRepresentation.IntertwiningMap
        (Representation.trivial (ZMod 2) G (ZMod 2))) ≤ 4 := by
  have hpow : Nat.card X = 2 ^ 3 := by simpa only [hcard] using (by decide : 8 = 2 ^ 3)
  simpa only [hcard] using
    primePower_permutationSubrepresentationHead_le_div (p := 2) hpow M

end SymmetricSubgroupAsymptotics

end
