import SymmetricSubgroupAsymptotics.GeneralFourTwoPointAction
import SymmetricSubgroupAsymptotics.BinaryFanoHeptadRepresentation
import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple
import Mathlib.Algebra.Group.Subgroup.Finite

/-! The already constructed heptad homomorphism is an actual isomorphism
A8 → GL(4,2): simplicity gives injectivity from one nonidentity matrix,
and both groups have order20160. Its inverse supplies an eight-point
permutation action for the actual matrix group. No ambient Cayley table
or subgroup classification is used, and matrix conjugators are retained. -/
set_option autoImplicit false
noncomputable section
open scoped Classical Pointwise
namespace SymmetricSubgroupAsymptotics.GeneralFourTwoAlternatingEquiv

abbrev Ambient := GeneralFourTwoMatrixEncoding.Ambient
abbrev Alternating := alternatingGroup (Fin 8)
abbrev LinearGroup := BinaryFourAffineImage.LinearGroup

private theorem b20_ne_one : BinaryFanoHeptadData.b20 ≠ 1 := by
  intro h
  have hv := congrArg (fun g : LinearGroup => g (![1,0,0,0] : Fin 4 → ZMod 2) 0) h
  change (0 : ZMod 2) = 1 at hv
  exact zero_ne_one hv

theorem hom8_injective : Function.Injective BinaryFanoHeptadRepresentation.hom8 := by
  letI := alternatingGroup.isSimpleGroup (α := Fin 8) (by norm_num)
  apply (MonoidHom.ker_eq_bot_iff BinaryFanoHeptadRepresentation.hom8).mp
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
      BinaryFanoHeptadRepresentation.hom8.ker inferInstance with h | h
  · exact h
  · have hb : BinaryFanoHeptadRepresentation.hom8 BinaryFanoHeptadGenerators.b8 = 1 := by
      change BinaryFanoHeptadGenerators.b8 ∈ BinaryFanoHeptadRepresentation.hom8.ker
      rw [h]
      trivial
    rw [BinaryFanoHeptadRepresentation.hom8_b8] at hb
    exact False.elim (b20_ne_one hb)

theorem alternating_card : Nat.card Alternating = 20160 := by
  rw [nat_card_alternatingGroup, Nat.card_fin]
  norm_num

theorem linear_card : Nat.card LinearGroup = 20160 :=
  (Nat.card_congr GeneralFourTwoPointAction.linearEquiv.toEquiv).symm.trans
    GeneralFourTwoMatrixEncoding.ambient_card

theorem hom8_bijective : Function.Bijective BinaryFanoHeptadRepresentation.hom8 := by
  letI : Finite LinearGroup := Finite.of_equiv Ambient
    GeneralFourTwoPointAction.linearEquiv.toEquiv
  apply (Nat.bijective_iff_injective_and_card _).mpr
  exact ⟨hom8_injective, alternating_card.trans linear_card.symm⟩

def alternatingLinearEquiv : Alternating ≃* LinearGroup :=
  MulEquiv.ofBijective BinaryFanoHeptadRepresentation.hom8 hom8_bijective

def matrixToAlternating : Ambient ≃* Alternating :=
  GeneralFourTwoPointAction.linearEquiv.trans alternatingLinearEquiv.symm

/-- The matrix chart recovers the very homomorphism used to construct it. -/
theorem hom8_matrixToAlternating (g : Ambient) :
    BinaryFanoHeptadRepresentation.hom8 (matrixToAlternating g) =
      GeneralFourTwoPointAction.linearEquiv g :=
  alternatingLinearEquiv.apply_symm_apply _

def eightAction : Ambient →* Equiv.Perm (Fin 8) :=
  (alternatingGroup (Fin 8)).subtype.comp matrixToAlternating.toMonoidHom

theorem eightAction_injective : Function.Injective eightAction :=
  Subtype.coe_injective.comp matrixToAlternating.injective

theorem eightAction_range : eightAction.range = alternatingGroup (Fin 8) := by
  ext p
  constructor
  · rintro ⟨g, rfl⟩
    exact (matrixToAlternating g).property
  · intro hp
    refine ⟨matrixToAlternating.symm ⟨p, hp⟩, ?_⟩
    exact congrArg Subtype.val (matrixToAlternating.apply_symm_apply ⟨p, hp⟩)

/-- Actual matrix conjugators become actual even permutation conjugators. -/
theorem map_conjugate (U : Subgroup Ambient) (c : Ambient) :
    (MulAut.conj c • U).map matrixToAlternating.toMonoidHom =
      MulAut.conj (matrixToAlternating c) • U.map matrixToAlternating.toMonoidHom := by
  have h : matrixToAlternating.toMonoidHom.comp (MulAut.conj c).toMonoidHom =
      (MulAut.conj (matrixToAlternating c)).toMonoidHom.comp
        matrixToAlternating.toMonoidHom := by
    apply MonoidHom.ext
    intro g
    change matrixToAlternating (c * g * c⁻¹) =
      matrixToAlternating c * matrixToAlternating g * (matrixToAlternating c)⁻¹
    rw [map_mul, map_mul, map_inv]
  change (U.map (MulAut.conj c).toMonoidHom).map matrixToAlternating.toMonoidHom =
    (U.map matrixToAlternating.toMonoidHom).map
      (MulAut.conj (matrixToAlternating c)).toMonoidHom
  rw [Subgroup.map_map, Subgroup.map_map, h]

end SymmetricSubgroupAsymptotics.GeneralFourTwoAlternatingEquiv
