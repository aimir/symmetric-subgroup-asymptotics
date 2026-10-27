import SymmetricSubgroupAsymptotics.ActualFullWreathFamily
import SymmetricSubgroupAsymptotics.ActualWreathCompressionTower
import SymmetricSubgroupAsymptotics.PermutationPrimeGroupRank

/-! Every member of the entire full-component family supplies a genuine
compression state. Its retained source degree is the regular-local
product degree, and its tuple enumerates the actual finite source. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.ActualFullWreathCompressionState
open PermutationalWreathProduct ActualFullWreathFamily

variable {R Q I : Type} [Group R] [Finite R] [Group Q] [Finite Q] [Fintype I]
    [Nonempty I] [MulAction Q I] [FaithfulSMul Q I] [MulAction.IsPretransitive Q I]

local instance wreathFinite : Finite (PermutationalWreathProduct R Q I) :=
  Finite.of_injective (fun w : PermutationalWreathProduct R Q I => (w.left,w.right))
    (by
      intro a b h
      apply PermutationalWreathProduct.ext
      · exact congrArg Prod.fst h
      · exact congrArg Prod.snd h)

def state (L : Family R Q I) : ActualWreathCompressionState Q I := by
  letI : MulAction L.val (R × I) := MulAction.compHom (R × I) L.val.subtype
  letI : FaithfulSMul L.val (R × I) := ⟨by
    intro g h hgh
    apply Subtype.ext
    exact eq_of_smul_eq_smul hgh⟩
  exact {
    A := L.val
    D := R
    groupA := inferInstance
    finiteA := inferInstance
    groupD := inferInstance
    finiteD := inferInstance
    rho := L.val.subtype
    rho_injective := Subtype.val_injective
    sourceDegree := Nat.card R*Nat.card I
    generatorCount := Nat.card L.val
    generators := (Finite.equivFin L.val).symm
    generators_full := by
      rw [Set.range_eq_univ.mpr (Finite.equivFin L.val).symm.surjective,
        Subgroup.closure_univ]
    sectionalRank := by
      intro p hp K
      simpa only [Nat.card_prod] using permutation_primeCharacterRank_le p K (R × I)
    top_surjective := ActualFullWreathFamily.top_surjective L
    top_pretransitive := inferInstance
    fullComponent := L.property.2 }

theorem state_rho (L : Family R Q I) : (state L).rho=L.val.subtype := rfl

end SymmetricSubgroupAsymptotics.ActualFullWreathCompressionState
