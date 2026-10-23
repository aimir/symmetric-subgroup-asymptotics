import SymmetricSubgroupAsymptotics.CFSGSubgroupConjugateOrbitCardinality

/-! Charge a conjugacy image along an actual group homomorphism to the
comap of the pointwise centralizer. No injectivity of the action hom is
required for this finite orbit bound. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGHomConjugateOrbitCardinality
open CFSGSubgroupConjugateOrbitCardinality

theorem image_card_mul_comap_centralizer_le {G H : Type*} [Group G] [Group H]
    [Finite G] (f : G →* H) (R : Subgroup H) :
    Nat.card (Set.range (fun g : G => R.map (MulAut.conj (f g)).toMonoidHom)) *
      Nat.card ((Subgroup.centralizer (R : Set H)).comap f) ≤ Nat.card G := by
  apply CFSGRightInvariantImageCardinality.image_card_mul_subgroup_le
  intro g c
  change R.map (MulAut.conj (f (g*c.val))).toMonoidHom = _
  rw [map_mul,conjugate_mul]
  exact congrArg (fun S : Subgroup H => S.map (MulAut.conj (f g)).toMonoidHom)
    (conjugate_eq_of_mem_normalizer R (f c.val)
      (Subgroup.centralizer_le_normalizer (R : Set H) c.property))

end SymmetricSubgroupAsymptotics.CFSGHomConjugateOrbitCardinality
