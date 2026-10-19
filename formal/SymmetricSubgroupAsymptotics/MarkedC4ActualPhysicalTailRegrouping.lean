import SymmetricSubgroupAsymptotics.MarkedC4ActualAbelianFactorSplit
import SymmetricSubgroupAsymptotics.MarkedC4ActualMarkedCaseIIFibre

/-! Regroup an ACTUAL physical source at any literal fully projecting tail.
Only physical coordinates are permuted; one global marker is preserved.
This constructs the R/P geometry required by ordinary RDT4.6. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.MarkedC4.ActualPhysicalTailRegrouping

variable {t : ℕ} (F : Fin t → Type) [∀ i,Group (F i)] (S : Finset (Fin t))
abbrev LeftLabels := {i : Fin t // i∉S}
abbrev RightLabels := {i : Fin t // i∈S}
def leftLabel (j : Fin (Fintype.card (LeftLabels S))) : LeftLabels S :=
  (Fintype.equivFin (LeftLabels S)).symm j
def rightLabel (j : Fin (Fintype.card (RightLabels S))) : RightLabels S :=
  (Fintype.equivFin (RightLabels S)).symm j
abbrev R (j : Fin (Fintype.card (LeftLabels S))) := F (leftLabel S j).val
abbrev P (j : Fin (Fintype.card (RightLabels S))) := F (rightLabel S j).val

variable (M : Type) [Group M]
def labelSplit : ((∀ i,F i) × M) ≃*
    (((∀ i : LeftLabels S,F i.val) × (∀ i : RightLabels S,F i.val)) × M) where
  toFun z := (((fun i => z.1 i.val),(fun i => z.1 i.val)),z.2)
  invFun z := ((fun i => if hi : i∈S then z.1.2 ⟨i,hi⟩ else z.1.1 ⟨i,hi⟩),z.2)
  left_inv z := by
    apply Prod.ext
    · funext i
      by_cases hi : i∈S <;> simp [hi]
    · rfl
  right_inv z := by
    apply Prod.ext
    · apply Prod.ext
      · funext i
        simp [i.property]
      · funext i
        simp [i.property]
    · rfl
  map_mul' _ _ := rfl

def split : ((∀ i,F i) × M) ≃* (((∀ i,R F S i) × (∀ j,P F S j)) × M) :=
  (labelSplit F S M).trans (MulEquiv.prodCongr
    (MulEquiv.prodCongr
      (ActualOrderedSubdirectTransport.physicalEquiv
        (Fintype.equivFin (LeftLabels S)).symm (fun i : LeftLabels S => F i.val))
      (ActualOrderedSubdirectTransport.physicalEquiv
        (Fintype.equivFin (RightLabels S)).symm (fun i : RightLabels S => F i.val)))
    (MulEquiv.refl M))

def Source (A : Subgroup ((∀ i,F i) × M)) :
    Subgroup (((∀ i,R F S i) × (∀ j,P F S j)) × M) := A.map (split F S M).toMonoidHom

def sourceEquiv (A : Subgroup ((∀ i,F i) × M)) : A ≃* Source F S M A :=
  A.equivMapOfInjective (split F S M).toMonoidHom (split F S M).injective

theorem full_left (A : Subgroup ((∀ i,F i) × M))
    (hfull : ∀ i,Function.Surjective (fun h : A => h.val.1 i))
    (j : Fin (Fintype.card (LeftLabels S))) :
    Function.Surjective (fun h : Source F S M A => h.val.1.1 j) := by
  intro g
  obtain ⟨a,ha⟩ := hfull (leftLabel S j).val g
  exact ⟨⟨split F S M a.val,⟨a.val,a.property,rfl⟩⟩,ha⟩

theorem full_right (A : Subgroup ((∀ i,F i) × M))
    (hfull : Function.Surjective (fun a : A => (fun i : RightLabels S => a.val.1 i.val))) :
    Function.Surjective (fun h : Source F S M A => h.val.1.2) := by
  intro p
  let eP := ActualOrderedSubdirectTransport.physicalEquiv
    (Fintype.equivFin (RightLabels S)).symm (fun i : RightLabels S => F i.val)
  let p' : ∀ i : RightLabels S,F i.val := eP.symm p
  obtain ⟨a,ha⟩ := hfull p'
  refine ⟨⟨split F S M a.val,⟨a.val,a.property,rfl⟩⟩,?_⟩
  change eP (fun i : RightLabels S => a.val.1 i.val)=p
  exact (congrArg eP ha).trans (eP.apply_symm_apply p)

end SymmetricSubgroupAsymptotics.MarkedC4.ActualPhysicalTailRegrouping
