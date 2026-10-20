import SymmetricSubgroupAsymptotics.MarkedC4ActualWordMenuPartition

/-! Global actual Hall-family cover by constructed physical order/tableau
menus. The finite alphabet is independent of the one global marker. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.MarkedC4.ActualGlobalMenuCover
open ActualWordMenuPartition

variable {t : ℕ} (F : Fin t → Type) [∀ i,Group (F i)] [∀ i,Finite (F i)]
  (weight : Fin t → ℕ) (E : Type) [CommGroup E]

abbrev ActualFamily := Σ H : Family F,AbelianProductGraphClassification.FullSecond E H.val
abbrev SplitFamily := Σ q : Menu F,Σ H : {H : Family F // key F weight H=q},
  AbelianProductGraphClassification.FullSecond E H.val.val
abbrev MenuCover := Σ q : Menu F,Σ U : MenuFamily F q,
  AbelianProductGraphClassification.FullSecond E U.val.val

def split : ActualFamily F E ≃ SplitFamily F weight E where
  toFun z := ⟨key F weight z.1,⟨⟨z.1,rfl⟩,z.2⟩⟩
  invFun z := ⟨z.2.1.val,z.2.2⟩
  left_inv z := by cases z; rfl
  right_inv z := by
    rcases z with ⟨q,⟨⟨H,hH⟩,J⟩⟩
    subst q
    rfl

def menuMap (z : SplitFamily F weight E) : MenuCover F E :=
  ⟨z.1,hallFibreMap F weight z.1 E z.2⟩

theorem menuMap_injective : Function.Injective (menuMap F weight E) := by
  rintro ⟨q,z⟩ ⟨q',z'⟩ he
  have hq : q=q' := congrArg Sigma.fst he
  subst q'
  have hz : z=z' := hallFibreMap_injective F weight q E (by
    simpa only [menuMap,Sigma.mk.inj_iff,heq_eq_eq,true_and] using he)
  subst z'
  rfl

def code : ActualFamily F E → MenuCover F E :=
  (menuMap F weight E) ∘ (split F weight E)

theorem code_injective : Function.Injective (code F weight E) :=
  (menuMap_injective F weight E).comp (split F weight E).injective

include weight in
/-- This counts the entire actual physical/Hall family, with one global
target E. It is an actual finite injection, not an enumeration premise. -/
theorem card_le_cover [Finite E] :
    Nat.card (ActualFamily F E)≤Nat.card (MenuCover F E) :=
  Nat.card_le_card_of_injective (code F weight E) (code_injective F weight E)

end SymmetricSubgroupAsymptotics.MarkedC4.ActualGlobalMenuCover
