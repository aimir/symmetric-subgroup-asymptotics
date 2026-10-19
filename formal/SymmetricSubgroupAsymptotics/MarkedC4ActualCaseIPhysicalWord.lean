import SymmetricSubgroupAsymptotics.MarkedC4ActualUniversalCaseINormalized
import SymmetricSubgroupAsymptotics.MarkedC4ActualFullPhysicalWordPeel

/-! Case-I endpoint for the literal physical-full marked word family.
The actual physical projection and its entire Hall fibre are constructed;
no product classification or encoding is supplied as an input. -/
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators
namespace SymmetricSubgroupAsymptotics.MarkedC4.ActualCaseIPhysicalWord
open ActualFullPhysicalWordPeel

variable {t : ℕ} (F : Fin t → Type) [∀ i,Group (F i)] [∀ i,Finite (F i)]
  (E : Type) [CommGroup E]

def physicalImage (J : Family F E) : Subgroup (∀ i,F i) :=
  J.val.map (MonoidHom.fst (∀ i,F i) E)
def inclusion (H : Subgroup (∀ i,F i)) : E × H →* (∀ i,F i) × E where
  toFun x := (x.2.val,x.1)
  map_one' := rfl
  map_mul' _ _ := rfl

def hall (J : Family F E) : AbelianProductGraphClassification.FullSecond E (physicalImage F E J) := by
  refine ⟨J.val.comap (inclusion F E (physicalImage F E J)),top_unique ?_⟩
  intro h hh
  obtain ⟨z,hz,hzh⟩ := h.property
  have he : inclusion F E (physicalImage F E J) (z.2,h)=z := Prod.ext hzh.symm rfl
  exact ⟨(z.2,h),he.symm ▸ hz,rfl⟩

def code (hbinary : ∀ i,IsPGroup 2 (F i)) (J : Family F E) :
    ActualGlobalMenuCover.ActualFamily F E := by
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  letI (i : Fin t) : Group.IsNilpotent (F i) := (hbinary i).isNilpotent
  have hfull : ∀ i,Function.Surjective
      (ActualSubdirectFiltration.coordinate F (physicalImage F E J) i) := by
    intro i g
    obtain ⟨h,hh⟩ := J.property i g
    exact ⟨⟨h.val.1,⟨h.val,h.property,rfl⟩⟩,hh⟩
  exact ⟨⟨physicalImage F E J,hfull,inferInstance⟩,hall F E J⟩

def decode (z : ActualGlobalMenuCover.ActualFamily F E) : Subgroup ((∀ i,F i) × E) :=
  z.2.val.map (inclusion F E z.1.val)

theorem recover (hbinary : ∀ i,IsPGroup 2 (F i)) (J : Family F E) :
    decode F E (code F E hbinary J)=J.val := by
  change (J.val.comap (inclusion F E (physicalImage F E J))).map
    (inclusion F E (physicalImage F E J))=J.val
  apply le_antisymm
  · exact Subgroup.map_comap_le (inclusion F E (physicalImage F E J)) J.val
  · intro z hz
    let h : physicalImage F E J := ⟨z.1,⟨z,hz,rfl⟩⟩
    exact ⟨(z.2,h),hz,rfl⟩

theorem code_injective (hbinary : ∀ i,IsPGroup 2 (F i)) :
    Function.Injective (code F E hbinary) := by
  intro J K he
  apply Subtype.ext
  exact (recover F E hbinary J).symm.trans ((congrArg (decode F E) he).trans (recover F E hbinary K))

/-- The literal marked-word Case-I count, including every vertical mark
subgroup, with a single global P(r) and an r-independent physical cost. -/
theorem marked_word_card_le (weight : Fin t → ℕ) (K : ℕ)
    (hK : ∀ i,Nat.card (F i)≤K) (hw : ∀ i,0<weight i)
    (hbinary : ∀ i,IsPGroup 2 (F i)) (hcard : ∀ i,Nat.card (F i)≤2^weight i)
    (hquarter : ∀ (i : Fin t) (V : Subgroup (F i)),V.Normal →
      (normalGen V : ℝ)≤(weight i : ℝ)/4)
    (m r : ℕ) (A : Type) [CommGroup A] [Finite A]
    (hA : HasExp2 A (2+m)) {a B : ℝ} (ha : 0≤a)
    (hAcard : (Nat.card A : ℝ)≤(2 : ℝ)^(a/2))
    (hlog : ∀ i,Real.logb 2 (Nat.card (F i))≤B) :
    (Nat.card (Family F (A × Multiplicative (Fin r → ZMod 4))) : ℝ)≤
      VerticalHallBase.polynomial r*
        ActualUniversalCaseINormalized.physicalCost t K m A B*
          (2 : ℝ)^markedF (a+∑ i : Fin t,(weight i : ℝ)) r := by
  have hactual : (Nat.card (Family F (A × Multiplicative (Fin r → ZMod 4))) : ℝ)≤
      Nat.card (ActualGlobalMenuCover.ActualFamily F
        (A × Multiplicative (Fin r → ZMod 4))) := by
    exact_mod_cast Nat.card_le_card_of_injective
      (code F (A × Multiplicative (Fin r → ZMod 4)) hbinary)
      (code_injective F (A × Multiplicative (Fin r → ZMod 4)) hbinary)
  exact hactual.trans (ActualUniversalCaseINormalized.actual_family_card_le
    F weight K hK hw hbinary hcard hquarter m r A hA ha hAcard hlog)

end SymmetricSubgroupAsymptotics.MarkedC4.ActualCaseIPhysicalWord
