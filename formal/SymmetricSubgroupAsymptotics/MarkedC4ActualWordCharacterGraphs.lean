import SymmetricSubgroupAsymptotics.MarkedC4ActualFullPhysicalWordPeel
import SymmetricSubgroupAsymptotics.MarkedC4SubgroupCharacterGraph
import SymmetricSubgroupAsymptotics.MarkedC4ActualGlobalMarkGeneratorRank

/-! Joint characters of all literal full physical sources inject into the
one marked physical family. Source multiplicity is consumed by the graph,
not charged a second time outside the fixed-word count. -/
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators
namespace SymmetricSubgroupAsymptotics.MarkedC4.ActualWordCharacterGraphs
open ActualGlobalMarkGeneratorRank
variable {t : ℕ} (F : Fin t → Type) [∀ i,Group (F i)] [∀ i,Finite (F i)]

abbrev Source := {H : Subgroup (∀ i,F i) //
  ∀ i,Function.Surjective (fun h : H => h.val i)}

variable (r : ℕ)
def join (H : Subgroup (∀ i,F i)) (f : Fin r → (H →* Multiplicative (ZMod 4))) :
    H →* Marks r where
  toFun h := Multiplicative.ofAdd (fun i => (f i h).toAdd)
  map_one' := by ext i; exact congrArg Multiplicative.toAdd (map_one (f i))
  map_mul' x y := by ext i; exact congrArg Multiplicative.toAdd (map_mul (f i) x y)

theorem join_injective (H : Subgroup (∀ i,F i)) : Function.Injective (join F r H) := by
  intro f g h
  funext i
  apply MonoidHom.ext
  intro x
  exact Multiplicative.toAdd.injective (congrFun (congrArg Multiplicative.toAdd (DFunLike.congr_fun h x)) i)

abbrev Joint := Σ H : Source F,Fin r → (H.val →* Multiplicative (ZMod 4))

def graphCode (z : Joint F r) : ActualFullPhysicalWordPeel.Family F (Marks r) := by
  refine ⟨SubgroupCharacterGraph.graph z.1.val (join F r z.1.val z.2),?_⟩
  intro i g
  obtain ⟨h,hh⟩ := z.1.property i g
  exact ⟨⟨SubgroupCharacterGraph.hom z.1.val (join F r z.1.val z.2) h,⟨h,rfl⟩⟩,hh⟩

theorem graphCode_injective : Function.Injective (graphCode F r) := by
  rintro ⟨⟨H,hH⟩,f⟩ ⟨⟨K,hK⟩,g⟩ he
  have hgraph : SubgroupCharacterGraph.code ⟨H,join F r H f⟩=
      SubgroupCharacterGraph.code ⟨K,join F r K g⟩ :=
    congrArg (fun z : ActualFullPhysicalWordPeel.Family F (Marks r) => z.val) he
  have hg := SubgroupCharacterGraph.code_injective hgraph
  have hHK : H=K := congrArg Sigma.fst hg
  subst K
  have hfg : join F r H f=join F r H g := eq_of_heq (Sigma.mk.inj hg).2
  have hf := join_injective F r H hfg
  subst g
  rfl

instance sourceFinite : Finite (Source F) := inferInstance
local instance sourceFintype : Fintype (Source F) := Fintype.ofFinite _
instance homFinite (H : Source F) : Finite (H.val →* Multiplicative (ZMod 4)) :=
  Finite.of_injective (fun f : H.val →* Multiplicative (ZMod 4) => (f : H.val → Multiplicative (ZMod 4))) DFunLike.coe_injective
instance jointFinite : Finite (Joint F r) := by
  unfold Joint
  haveI (H : Source F) : Finite (H.val →* Multiplicative (ZMod 4)) :=
    Finite.of_injective (fun f : H.val →* Multiplicative (ZMod 4) => (f : H.val → Multiplicative (ZMod 4))) DFunLike.coe_injective
  infer_instance

theorem moment_le :
    (∑ H : Source F,(Nat.card (H.val →* Multiplicative (ZMod 4)) : ℝ)^r) ≤
      Nat.card (ActualFullPhysicalWordPeel.Family F (Marks r)) := by
  letI : Fintype (Source F) := Fintype.ofFinite _
  have hc : Nat.card (Joint F r)=∑ H : Source F,Nat.card (H.val →* Multiplicative (ZMod 4))^r := by
    unfold Joint
    rw [Nat.card_sigma]
    simp only [Nat.card_fun,Nat.card_fin]
  have hi := Nat.card_le_card_of_injective (graphCode F r) (graphCode_injective F r)
  rw [hc] at hi
  exact_mod_cast hi

end SymmetricSubgroupAsymptotics.MarkedC4.ActualWordCharacterGraphs
