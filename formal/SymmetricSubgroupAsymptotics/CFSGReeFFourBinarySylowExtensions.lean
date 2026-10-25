import SymmetricSubgroupAsymptotics.FiniteNormalSylowPairExtension
import SymmetricSubgroupAsymptotics.CFSGReeFFourBinaryOuterSaving

/-! Exact extensions of binary derived Sylows to the SAME full fixed group.
The actual abelianization bound controls the ambient intersection by two.
No automorphism is extended and no ambient intersection is asserted trivial. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourBinarySylowExtensions
open CFSGReeFFourFixedModelEquivalence CFSGReeFFourFixedAmbientHom
open CFSGReeFFourBinaryOuterSaving FiniteNormalSylowPairExtension
local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
private instance fixedFinite : Finite (originalModelFixed 0) :=
  Finite.of_injective (fixedAmbientHom 0) (fixedAmbientHom_injective 0)

theorem derived_index_le_two : (commutator (originalModelFixed 0)).index ≤ 2 :=
  abelianization_card_le_two

theorem ambient_intersection_card_le_two
    (P Q : Subgroup (originalModelFixed 0))
    (h : P.comap (commutator (originalModelFixed 0)).subtype ⊓
      Q.comap (commutator (originalModelFixed 0)).subtype = ⊥) :
    Nat.card (P ⊓ Q : Subgroup (originalModelFixed 0)) ≤ 2 :=
  (card_inf_le_index_of_disjoint_comap (commutator (originalModelFixed 0)) P Q h).trans
    derived_index_le_two

theorem exists_sylow_extensions
    (P Q : Sylow 2 (commutator (originalModelFixed 0)))
    (h : (P : Subgroup (commutator (originalModelFixed 0))) ⊓
      (Q : Subgroup (commutator (originalModelFixed 0))) = ⊥) :
    ∃ R S : Sylow 2 (originalModelFixed 0),
      (R : Subgroup (originalModelFixed 0)).comap
        (commutator (originalModelFixed 0)).subtype = (P : Subgroup _) ∧
      (S : Subgroup (originalModelFixed 0)).comap
        (commutator (originalModelFixed 0)).subtype = (Q : Subgroup _) ∧
      Nat.card ((R : Subgroup (originalModelFixed 0)) ⊓
        (S : Subgroup (originalModelFixed 0)) : Subgroup (originalModelFixed 0)) ≤ 2 := by
  obtain ⟨R, S, hR, hS, hc⟩ :=
    exists_sylow_pair (commutator (originalModelFixed 0)) P Q h
  exact ⟨R, S, hR, hS, hc.trans derived_index_le_two⟩

end SymmetricSubgroupAsymptotics.CFSGReeFFourBinarySylowExtensions
