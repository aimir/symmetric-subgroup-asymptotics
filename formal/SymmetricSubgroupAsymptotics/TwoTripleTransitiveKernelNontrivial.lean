import SymmetricSubgroupAsymptotics.TwoTripleFullUpperForcesFullWreath
import SymmetricSubgroupAsymptotics.PrimitiveSixFinalPublishedNormalGenerators

/-! A transitive six-point epimorphic image excludes a binary actual
two-triple group. Consequently the original ternary upper kernel has a
nonidentity element. No Cauchy search or group enumeration is required. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.TwoTripleFullUpperForcesFullWreath

private def binaryCoordinates : Upper ≃ (Binary × Binary) × Binary where
  toFun g := (g.left,g.right)
  invFun p := ⟨p.1,p.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem upper_isPGroup : IsPGroup 2 Upper := by
  have hbin : Nat.card Binary = 2 :=
    (Nat.card_congr Multiplicative.toAdd).trans (Nat.card_zmod 2)
  apply IsPGroup.of_card (n := 3)
  rw [Nat.card_congr binaryCoordinates,Nat.card_prod,Nat.card_prod,hbin]
  norm_num

theorem kernel_nontrivial_of_transitive_image
    (H : Subgroup Model) (P : Subgroup (Equiv.Perm (Fin 6)))
    [MulAction.IsPretransitive P (Fin 6)]
    (pi : H →* P) (hpi : Function.Surjective pi) :
    ∃ g : Model, g ∈ H ∧ upper g = 1 ∧ g ≠ 1 := by
  let f : H →* Upper := upper.comp H.subtype
  have hne : f.ker ≠ ⊥ := by
    intro hbot
    have htwo : IsPGroup 2 H := upper_isPGroup.of_injective f (f.ker_eq_bot_iff.mp hbot)
    exact PrimitiveSixFinalPublishedNormalGenerators.not_isPGroup P
      (htwo.of_surjective pi hpi)
  obtain ⟨g,hg,hgne⟩ := f.ker.bot_or_exists_ne_one.resolve_left hne
  refine ⟨g,g.2,hg,?_⟩
  intro he
  exact hgne (Subtype.ext he)

end SymmetricSubgroupAsymptotics.TwoTripleFullUpperForcesFullWreath
