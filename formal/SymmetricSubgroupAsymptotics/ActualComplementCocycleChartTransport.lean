import SymmetricSubgroupAsymptotics.ActualComplementSubgroupCocycleCode

/-! Transport the actual complement code through the literal kernel chart.
The coordinate automorphism action is CONSTRUCTED from actual conjugation;
it is not an independent replacement action or splitting assumption. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.ActualComplementCocycleChartTransport
open TwistedMonomialCocycleFrame ActualComplementSubgroupCocycleCode

variable {Q N B : Type*} [Group Q] [Group N] [Group B]

def transportAction (e : N ≃* B) (α : Q →* MulAut N) : Q →* MulAut B where
  toFun q := (e.symm.trans (α q)).trans e
  map_one' := by
    apply MulEquiv.ext
    intro b
    change e (α 1 (e.symm b))=b
    rw [map_one,MulAut.one_apply,e.apply_symm_apply]
  map_mul' p q := by
    apply MulEquiv.ext
    intro b
    change e (α (p*q) (e.symm b))=
      e (α p (e.symm (e (α q (e.symm b)))))
    rw [map_mul,e.symm_apply_apply]
    rfl

def transportCocycle (e : N ≃* B) (α : Q →* MulAut N) (c : Cocycle α) :
    Cocycle (transportAction e α) :=
  ⟨fun q => e (c.val q),by
    intro p q
    change e (c.val (p*q))=e (c.val p)*e (α p (e.symm (e (c.val q))))
    rw [c.property,map_mul,e.symm_apply_apply]⟩

theorem transportCocycle_injective (e : N ≃* B) (α : Q →* MulAut N) :
    Function.Injective (transportCocycle e α) := by
  intro c d h
  apply Subtype.ext
  funext q
  apply e.injective
  exact congrArg (fun z : Cocycle (transportAction e α) => z.val q) h

variable {E : Type*} [Group E] (π : E →* Q)
    (L0 : ActualComplementSubgroupCocycleCode.Family π) (e : π.ker ≃* B)

def coordinateAction : Q →* MulAut B := transportAction e (baselineAction π L0)

def chartCode (L : ActualComplementSubgroupCocycleCode.Family π) :
    Cocycle (coordinateAction π L0 e) :=
  transportCocycle e (baselineAction π L0) (cocycleCode π L0 L)

theorem chartCode_injective : Function.Injective (chartCode π L0 e) :=
  (transportCocycle_injective e (baselineAction π L0)).comp (cocycleCode_injective π L0)

def filteredChartCode (P : Cocycle (coordinateAction π L0 e) → Prop)
    (L : {L : ActualComplementSubgroupCocycleCode.Family π // P (chartCode π L0 e L)}) :
    {c : Cocycle (coordinateAction π L0 e) // P c} :=
  ⟨chartCode π L0 e L.val,L.property⟩

theorem filteredChartCode_injective (P : Cocycle (coordinateAction π L0 e) → Prop) :
    Function.Injective (filteredChartCode π L0 e P) := by
  intro L M h
  exact Subtype.ext (chartCode_injective π L0 e (congrArg Subtype.val h))

theorem card_filtered_family_le (P : Cocycle (coordinateAction π L0 e) → Prop)
    [Finite {c : Cocycle (coordinateAction π L0 e) // P c}] :
    Nat.card {L : ActualComplementSubgroupCocycleCode.Family π // P (chartCode π L0 e L)}≤
      Nat.card {c : Cocycle (coordinateAction π L0 e) // P c} :=
  Nat.card_le_card_of_injective (filteredChartCode π L0 e P)
    (filteredChartCode_injective π L0 e P)

end SymmetricSubgroupAsymptotics.ActualComplementCocycleChartTransport
