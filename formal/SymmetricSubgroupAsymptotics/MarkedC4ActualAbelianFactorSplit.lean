import SymmetricSubgroupAsymptotics.MarkedC4ActualCaseIPhysicalWord

/-! Construct the ACTUAL abelian quotient block before Case-I/II bounds.
Original labels and physical degrees are retained under the split. Only
the genuinely nonabelian factors will receive the quarter hypothesis. -/
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators
namespace SymmetricSubgroupAsymptotics.MarkedC4.ActualAbelianFactorSplit
open ActualFullPhysicalWordPeel

variable {t : ℕ} (F : Fin t → Type) [∀ i,Group (F i)] [∀ i,Finite (F i)]
def Abelian (i : Fin t) : Prop := ∀ x y : F i,x*y=y*x
abbrev AbelianLabels := {i : Fin t // Abelian F i}
abbrev NonabelianLabels := {i : Fin t // ¬Abelian F i}
local instance : Fintype (AbelianLabels F) := inferInstance
local instance : Fintype (NonabelianLabels F) := inferInstance

abbrev AbelianFactor (i : AbelianLabels F) := F i.val
instance abelianCommGroup (i : AbelianLabels F) : CommGroup (AbelianFactor F i) :=
  { (inferInstance : Group (F i.val)) with mul_comm := i.property }
abbrev AbelianBlock := ∀ i : AbelianLabels F,AbelianFactor F i
def label (j : Fin (Fintype.card (NonabelianLabels F))) : NonabelianLabels F :=
  (Fintype.equivFin (NonabelianLabels F)).symm j
abbrev NonabelianFactors (j : Fin (Fintype.card (NonabelianLabels F))) := F (label F j).val

variable (M : Type) [Group M]
def labelSplit : ((∀ i,F i) × M) ≃*
    (∀ j : NonabelianLabels F,F j.val) × (AbelianBlock F × M) where
  toFun z := ((fun j => z.1 j.val),((fun i => z.1 i.val),z.2))
  invFun z := ((fun i => if hi : Abelian F i then z.2.1 ⟨i,hi⟩
    else z.1 ⟨i,hi⟩),z.2.2)
  left_inv z := by
    apply Prod.ext
    · funext i
      by_cases hi : Abelian F i <;> simp [hi]
    · rfl
  right_inv z := by
    apply Prod.ext
    · funext j
      simp [j.property]
    · apply Prod.ext
      · funext i
        simp [i.property]
      · rfl
  map_mul' _ _ := rfl

def split : ((∀ i,F i) × M) ≃* (∀ j,NonabelianFactors F j) × (AbelianBlock F × M) :=
  (labelSplit F M).trans (MulEquiv.prodCongr
    (ActualOrderedSubdirectTransport.physicalEquiv
      (Fintype.equivFin (NonabelianLabels F)).symm (fun i : NonabelianLabels F => F i.val))
    (MulEquiv.refl (AbelianBlock F × M)))

def code (J : Family F M) : Family (NonabelianFactors F) (AbelianBlock F × M) := by
  refine ⟨J.val.map (split F M).toMonoidHom,?_⟩
  intro j g
  obtain ⟨h,hh⟩ := J.property (label F j).val g
  exact ⟨⟨split F M h.val,⟨h.val,h.property,rfl⟩⟩,hh⟩

theorem code_injective : Function.Injective (code F M) := by
  intro J K he
  apply Subtype.ext
  exact Subgroup.map_injective (f := (split F M).toMonoidHom) (split F M).injective
    (congrArg Subtype.val he)

def abelianDegree (weight : Fin t → ℕ) : ℝ := ∑ i : AbelianLabels F,(weight i.val : ℝ)
def nonabelianWeight (weight : Fin t → ℕ)
    (j : Fin (Fintype.card (NonabelianLabels F))) : ℕ := weight (label F j).val

theorem degree_eq (weight : Fin t → ℕ) :
    abelianDegree F weight+∑ j : Fin (Fintype.card (NonabelianLabels F)),
      (nonabelianWeight F weight j : ℝ)=∑ i : Fin t,(weight i : ℝ) := by
  have hn : (∑ j : Fin (Fintype.card (NonabelianLabels F)),
      (nonabelianWeight F weight j : ℝ))=∑ i : NonabelianLabels F,(weight i.val : ℝ) :=
    Fintype.sum_equiv (Fintype.equivFin (NonabelianLabels F)).symm _ _ (fun _ => rfl)
  rw [hn]
  exact Fintype.sum_subtype_add_sum_subtype (Abelian F) (fun i => (weight i : ℝ))

theorem abelian_order_cap (weight : Fin t → ℕ)
    (hcard : ∀ i,Abelian F i →(Nat.card (F i) : ℝ)≤(2 : ℝ)^((weight i : ℝ)/2)) :
    (Nat.card (AbelianBlock F) : ℝ)≤(2 : ℝ)^(abelianDegree F weight/2) := by
  change (Nat.card (∀ i : AbelianLabels F,AbelianFactor F i) : ℝ)≤_
  rw [Nat.card_pi,Nat.cast_prod]
  calc
    _≤∏ i : AbelianLabels F,(2 : ℝ)^((weight i.val : ℝ)/2) := by
      apply Finset.prod_le_prod
      · intro i hi
        exact Nat.cast_nonneg _
      · intro i hi
        exact hcard i.val i.property
    _=(2 : ℝ)^(∑ i : AbelianLabels F,(weight i.val : ℝ)/2) :=
      (Real.rpow_sum_of_pos (by norm_num : (0 : ℝ)<2) _ _).symm
    _=_ := by rw [← Finset.sum_div]; rfl

theorem abelian_exponent (m : ℕ) (hExp : ∀ i,HasExp2 (F i) (2+m)) :
    HasExp2 (AbelianBlock F) (2+m) := by
  intro x
  funext i
  exact hExp i.val (x i)

end SymmetricSubgroupAsymptotics.MarkedC4.ActualAbelianFactorSplit
