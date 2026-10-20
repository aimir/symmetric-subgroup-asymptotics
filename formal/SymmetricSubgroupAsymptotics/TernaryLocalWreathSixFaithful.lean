import SymmetricSubgroupAsymptotics.TernaryLocalWreathProperRelativeHead
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.TernaryLocalWreathSixFaithful
local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
open SemidirectProduct
open SixPairLocalWreathSocles (Local Model localAction literalAction pairChart)

theorem local_injective : Function.Injective localAction := by
  have h : ∀ (v w : TernarySwapUpperNormalGenerators.Ternary)
      (b c : TernarySwapUpperNormalGenerators.Binary),
      (∀ x : ZMod 3,localAction ⟨v,b⟩ x=localAction ⟨w,c⟩ x) → v=w ∧ b=c := by
    decide +kernel
  rintro ⟨v,b⟩ ⟨w,c⟩ he
  have hh := h v w b c (fun x => congrArg (fun p : Equiv.Perm (ZMod 3) => p x) he)
  exact SemidirectProduct.ext hh.1 hh.2

theorem action_injective : Function.Injective literalAction := by
  intro g h he
  apply C2Wreath.action_injective localAction local_injective
  exact pairChart.permCongrHom.injective he

def canonicalEquiv : Model ≃* literalAction.range :=
  MulEquiv.ofBijective literalAction.rangeRestrict
    ⟨fun _ _ h => action_injective (congrArg Subtype.val h),literalAction.rangeRestrict_surjective⟩

theorem proper_head {B : Type} [Group B] [Finite B] (e : B ≃* Model)
    (M : Subgroup B) [M.Normal] (hne : M≠⊤) :
    Module.finrank (ZMod 2) (primeRelativeCharacters 2 M)≤1 := by
  let I := M.map e.toMonoidHom
  letI : I.Normal := Subgroup.Normal.map inferInstance e.toMonoidHom e.surjective
  have he : I.map e.symm.toMonoidHom=M := by
    change (M.map e.toMonoidHom).map e.symm.toMonoidHom=M
    rw [Subgroup.map_map]
    have hid : e.symm.toMonoidHom.comp e.toMonoidHom=MonoidHom.id _ := by
      ext x
      exact e.symm_apply_apply x
    rw [hid,Subgroup.map_id]
  have hi : I≠⊤ := by
    intro h
    apply hne
    rw [← he,h,Subgroup.map_top_of_surjective _ e.symm.surjective]
  exact (relativeCharacterAmbientCongr 2 e M I rfl).finrank_eq.symm.le.trans
    (TernaryLocalWreathProperRelativeHead.proper_head I hi)
end SymmetricSubgroupAsymptotics.TernaryLocalWreathSixFaithful
