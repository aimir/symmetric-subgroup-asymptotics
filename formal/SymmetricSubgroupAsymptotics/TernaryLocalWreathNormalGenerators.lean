import SymmetricSubgroupAsymptotics.TernarySwapUpperNormalGenerators
import SymmetricSubgroupAsymptotics.PrimePairWreathNormalGenerators

/-! Two normal generators for the wreath of two ternary affine lines.
The actual local C3 kernel covers every nontrivial local normal subgroup.
The existing wreath normal-cover theorem therefore transfers the bound
from C2 wreath C2 without adding a position. No normal lattice is listed. -/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.TernaryLocalWreathNormalGenerators

open SemidirectProduct TernarySwapUpperNormalGenerators

abbrev Local := Upper true
abbrev Model := C2Wreath.W Local

def localTranslation : Local := inl (Multiplicative.ofAdd (1 : ZMod 3))
def localReflection : Local := inr (Multiplicative.ofAdd (1 : ZMod 2))

theorem localTranslation_ne_one : localTranslation ≠ 1 := by decide +kernel

theorem local_center : Subgroup.center Local = ⊥ := by
  apply le_antisymm ?_ bot_le
  intro g hg
  have ht : g ∈ IrreducibleAbelianSemidirect.translations inversionAction :=
    IrreducibleAbelianSemidirect.selfCentralizing inversionAction
      inversionAction_injective g (fun v _ => (Subgroup.mem_center_iff.mp hg v).symm)
  obtain ⟨v,rfl⟩ := ht
  have hc := congrArg SemidirectProduct.left
    (Subgroup.mem_center_iff.mp hg localReflection)
  change (1 : Ternary) * v⁻¹ = v * 1 at hc
  have hi : v⁻¹ = v := by simpa only [one_mul,mul_one] using hc
  have htest : ∀ a : ZMod 3, -a = a → a = 0 := by
    decide +kernel
  have hv : v = 1 := Multiplicative.toAdd.injective
    (htest v.toAdd (congrArg Multiplicative.toAdd hi))
  exact Subgroup.mem_bot.mpr (by rw [hv,map_one]; rfl)

theorem local_kernel_ne_bot : (rightHom : Local →* Binary).ker ≠ ⊥ := by
  intro hbot
  have hm : localTranslation ∈ (rightHom : Local →* Binary).ker := rfl
  exact localTranslation_ne_one (Subgroup.mem_bot.mp (hbot ▸ hm))

theorem normal_generating_pairs (N : Subgroup Model) (hN : N.Normal) :
    ∃ x : Fin 2 → Model, Subgroup.normalClosure (Set.range x) = N := by
  letI : Nontrivial Local := ⟨⟨localTranslation,1,localTranslation_ne_one⟩⟩
  apply C2Wreath.normal_generating_tuples_of_local_normal_cover
    (rightHom : Local →* Binary) rightHom_surjective local_center
    local_kernel_ne_bot ?_ (by decide) (PrimePairWreathNormalGenerators.normal_generating_pairs 2)
    N hN
  intro K hK hKb
  exact IrreducibleAbelianSemidirect.normal_cover inversionAction
    inversionAction_injective (ternary_irreducible inversionAction) K hK hKb

theorem normalGen_le (N : Subgroup Model) [N.Normal] : MarkedC4.normalGen N ≤ 2 := by
  obtain ⟨x,hx⟩ := normal_generating_pairs N inferInstance
  exact normalGen_le_of_fin_tuple x hx

theorem quotientSocle (N : Subgroup Model) [N.Normal] :
    SocleNormalGeneratorBound (Model ⧸ N) 2 :=
  quotientSocleNormalGeneratorBound_of_normal_generating_tuples normal_generating_pairs N

end SymmetricSubgroupAsymptotics.TernaryLocalWreathNormalGenerators

end
