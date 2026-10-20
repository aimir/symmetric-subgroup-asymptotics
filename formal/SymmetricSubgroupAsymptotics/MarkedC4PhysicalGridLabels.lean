import SymmetricSubgroupAsymptotics.MarkedC4ActiveFiberPermutation
import Mathlib.Data.Fintype.EquivFin

/-! Concrete original-point labels for Cartesian orbit grids. Singleton
coordinates use a sentinel; active coordinates use their actual compressed
support label. Both the label map and its injectivity are constructed. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.MarkedC4.PhysicalGridLabels
variable {I : Type} [Fintype I] (F : I → Type) [∀ i, Fintype (F i)]

abbrev Active := ActiveFiberPermutation.Support F
local instance : Fintype (Active F) := Fintype.ofFinite _

def activeLabel (i : I) (x : F i) : ℕ :=
  if hi : Nat.card (F i)=1 then 0 else
    (Fintype.equivFin (Active F) ⟨i,⟨x,hi⟩⟩).val+1

theorem activeLabel_injective (i : I) : Function.Injective (activeLabel F i) := by
  intro x y h
  by_cases hi : Nat.card (F i)=1
  · haveI : Subsingleton (F i) := (Nat.card_eq_one_iff_unique.mp hi).1
    exact Subsingleton.elim _ _
  · simp only [activeLabel,dif_neg hi] at h
    have hval := Nat.add_right_cancel h
    have he := (Fintype.equivFin (Active F)).injective (Fin.ext hval)
    have hx : (⟨x,hi⟩ : {x : F i // Nat.card (F i)≠1})=⟨y,hi⟩ := by
      simpa only [Sigma.mk.inj_iff,heq_eq_eq,true_and] using he
    exact congrArg Subtype.val hx

theorem activeLabel_le_card (i : I) (x : F i) :
    activeLabel F i x≤Fintype.card (Active F) := by
  unfold activeLabel
  split_ifs with hi
  · exact Nat.zero_le _
  · exact Nat.succ_le_of_lt (Fintype.equivFin (Active F) ⟨i,⟨x,hi⟩⟩).isLt

variable (A B : I → Type) [∀ i, Fintype (A i)] [∀ i, Fintype (B i)]

def labels (z : Σ i : I, A i × B i) : ℕ × ℕ × ℕ :=
  ((Fintype.equivFin I z.1).val,activeLabel A z.1 z.2.1,activeLabel B z.1 z.2.2)

theorem labels_injective : Function.Injective (labels A B) := by
  rintro ⟨i,a,d⟩ ⟨j,a',d'⟩ h
  have hij : i=j := (Fintype.equivFin I).injective
    (Fin.ext (congrArg (fun z : ℕ × ℕ × ℕ => z.1) h))
  cases hij
  have ha : a=a' := activeLabel_injective A i
    (congrArg (fun z : ℕ × ℕ × ℕ => z.2.1) h)
  have hd : d=d' := activeLabel_injective B i
    (congrArg (fun z : ℕ × ℕ × ℕ => z.2.2) h)
  cases ha
  cases hd
  rfl

/-- These are all possible original-label codes at physical degree b.
No subgroup enumeration or selected capacity is built into the alphabet. -/
abbrev Code (b : ℕ) := Fin b → Fin (b+1) × Fin (b+1) × Fin (b+1)

theorem card_code (b : ℕ) : Fintype.card (Code b)=(b+1)^(3*b) := by
  simp only [Code,Fintype.card_fun,Fintype.card_prod,Fintype.card_fin]
  rw [show (b+1)*((b+1)*(b+1))=(b+1)^3 by ring,← pow_mul]

def boundedLabels {b : ℕ}
    (hI : Fintype.card I≤b)
    (hA : Fintype.card (Active A)≤b) (hB : Fintype.card (Active B)≤b)
    (z : Σ i : I, A i × B i) : Fin (b+1) × Fin (b+1) × Fin (b+1) :=
  (⟨(Fintype.equivFin I z.1).val,by
      have := (Fintype.equivFin I z.1).isLt; omega⟩,
   ⟨activeLabel A z.1 z.2.1,by have := activeLabel_le_card A z.1 z.2.1; omega⟩,
   ⟨activeLabel B z.1 z.2.2,by have := activeLabel_le_card B z.1 z.2.2; omega⟩)

theorem boundedLabels_injective {b : ℕ}
    (hI : Fintype.card I≤b)
    (hA : Fintype.card (Active A)≤b) (hB : Fintype.card (Active B)≤b) :
    Function.Injective (boundedLabels A B hI hA hB) := by
  intro z w h
  apply labels_injective A B
  exact congrArg (fun z : Fin (b+1) × Fin (b+1) × Fin (b+1) =>
    (z.1.val,z.2.1.val,z.2.2.val)) h
end SymmetricSubgroupAsymptotics.MarkedC4.PhysicalGridLabels
