import SymmetricSubgroupAsymptotics.BinaryRegularKleinWreathCoordinates

/-! A nonconstant equality partition invariant under the actual regular
Klein translations admits two colors separating every equality class.
Only four-point geometry is checked; no subgroup/action census is used. -/
set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.RegularKleinKernelClassColoring
abbrev R := BinaryRegularKleinWreath.R
local instance : Fintype R := BinaryRegularKleinWreath.rFintype
local instance : DecidableEq R := BinaryRegularKleinWreath.rDecidableEq

private def pairColor (h i : R) : Fin 2 :=
  ⟨(if h.toAdd 0=1 then i.toAdd 1+h.toAdd 1*i.toAdd 0 else i.toAdd 0).val,
    ZMod.val_lt _⟩

private theorem pairColor_fiber : ∀ h : R, h≠1 → ∀ i j : R,
    pairColor h i=pairColor h j → i=j ∨ j=h*i := by decide +kernel

/-- A translation taking one partition class to another supplies two-point
fibres, each meeting every equality class in at most one point. -/
theorem exists_two_color {A : Type} (f : R → A)
    (hinvariant : ∀ r i j, f i=f j → f (r*i)=f (r*j))
    (hne : ¬ ∀ i, f i=f 1) :
    ∃ color : R → Fin 2, ∀ i j, f i=f j → color i=color j → i=j := by
  obtain ⟨h,hh⟩ := not_forall.mp hne
  have hh1 : h≠1 := by intro he; subst h; exact hh rfl
  have hsep (i : R) : f i≠f (h*i) := by
    intro he
    have hs := hinvariant i⁻¹ i (h*i) he
    have hs' : f 1=f h := by
      simpa only [inv_mul_cancel,mul_left_comm,mul_assoc,mul_inv_cancel,
        mul_one,one_mul] using hs
    exact hh hs'.symm
  refine ⟨pairColor h,?_⟩
  intro i j hij hc
  obtain he | he := pairColor_fiber h hh1 i j hc
  · exact he
  · subst j
    exact (hsep i hij).elim

end SymmetricSubgroupAsymptotics.RegularKleinKernelClassColoring
