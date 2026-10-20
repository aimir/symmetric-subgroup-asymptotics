import SymmetricSubgroupAsymptotics.TwoBlockWreathNormalGenerators
import SymmetricSubgroupAsymptotics.BinaryTopNormalizerOrbitHead
import SymmetricSubgroupAsymptotics.OriginalMinimalBlock
import Mathlib.GroupTheory.Perm.Finite

/-! Exact two-block action consumer. A local all-normal bound of two gives
relative rank at most five in the original group. The actual binary top
gives head at most four in every original local plane frame, hence a
nine-slot total. The local normal-generation theorem is a genuine remaining
input until the eligible primitive-eight components have been bound. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SymmetricSubgroupAsymptotics.OriginalMinimalBlock

local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

variable {G X : Type} [Group G] [Finite G] [MulAction G X]
    [MulAction.IsPretransitive G X] [FaithfulSMul G X] [Finite X]
    {x₀ : X} (D : OriginalMinimalBlock (A := G) x₀)

theorem twoBlock_top_card_dvd_two (hs : Nat.card D.Points = 2) :
    Nat.card D.Top ∣ 2 := by
  have h := D.Top.card_subgroup_dvd_card
  rw [Nat.card_perm, hs] at h
  norm_num at h
  exact h

theorem twoBlock_top_isPGroup (hs : Nat.card D.Points = 2) : IsPGroup 2 D.Top := by
  have h : Nat.card D.Top ∣ 2 ^ 1 := by
    simpa only [pow_one] using D.twoBlock_top_card_dvd_two hs
  obtain ⟨n, _, hn⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h
  exact IsPGroup.of_card hn

theorem twoBlock_normal_generating_tuples {a : ℕ} (hs : Nat.card D.Points = 2)
    (hL : ∀ N : Subgroup D.Component, N.Normal →
      ∃ x : Fin a → D.Component, Subgroup.normalClosure (Set.range x) = N) :
    ∀ N : Subgroup G, N.Normal →
      ∃ x : Fin (a + a + 1) → G, Subgroup.normalClosure (Set.range x) = N := by
  letI : IsCyclic D.Top := isCyclic_of_card_dvd_prime (D.twoBlock_top_card_dvd_two hs)
  exact TwoBlockWreathNormalGenerators.normal_generating_tuples
    (ActualBlockWreathEmbedding.embedding D.map D.map_equivariant D.base)
    hs (ActualBlockWreathEmbedding.embedding_injective D.map D.map_equivariant D.base)
    D.topMap.rangeRestrict_surjective
    (ActualBlockWreathEmbedding.fullComponent D.map D.map_equivariant D.base) hL

theorem twoBlock_relativeHead_le {a : ℕ} (hs : Nat.card D.Points = 2)
    (hL : ∀ N : Subgroup D.Component, N.Normal →
      ∃ x : Fin a → D.Component, Subgroup.normalClosure (Set.range x) = N)
    (N : Subgroup G) [N.Normal] :
    Module.finrank (ZMod 2) (primeRelativeCharacters 2 N) ≤ a + a + 1 := by
  obtain ⟨z, hz⟩ := D.twoBlock_normal_generating_tuples hs hL N inferInstance
  exact primeRelativeHead_le_normal_generating_tuple 2 N z hz

/-- The entire two-block frame bound is on the original group and the
original point stabilizer; the local component premise concerns only the
literal eight-point primitive component when this is used at degree16. -/
theorem twoBlock_frame_sum_le_nine (hs : Nat.card D.Points = 2)
    (hX : Nat.card X = 16)
    (hL : ∀ N : Subgroup D.Component, N.Normal →
      ∃ z : Fin 2 → D.Component, Subgroup.normalClosure (Set.range z) = N)
    {C V : Type} [Group C] [Finite C] [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V]
    (x : X) (f : MulAction.stabilizer G x →* C) (hf : Function.Surjective f)
    (rho : Representation (ZMod 2) C V)
    (hC : Nat.card C = 3 ∨ Nat.card C = 6)
    (hdim : Module.finrank (ZMod 2) V = 2) (hrho : Function.Injective rho)
    (N : Subgroup G) [N.Normal]
    (B : Subrepresentation (Representation.coind (MulAction.stabilizer G x).subtype
      (rho.comp f))) :
    Module.finrank (ZMod 2) (primeRelativeCharacters 2 N) +
      Module.finrank (ZMod 2)
        (B.toRepresentation.IntertwiningMap (Representation.trivial (ZMod 2) G (ZMod 2)))
        ≤ 9 := by
  letI : Nontrivial D.Points := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  letI : MulAction.IsPretransitive D.Top D.Points := D.top_pretransitive
  have hn := D.twoBlock_relativeHead_le hs hL N
  have hb := BinaryTopNormalizerOrbitHead.head_le_four_on_points x hX
    D.topMap.rangeRestrict D.topMap.rangeRestrict_surjective (D.twoBlock_top_isPGroup hs)
    (fun _ _ => rfl) D.map D.map_equivariant f hf rho hC hdim hrho B
  omega

end SymmetricSubgroupAsymptotics.OriginalMinimalBlock

end
