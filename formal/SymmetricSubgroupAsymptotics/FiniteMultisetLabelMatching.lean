import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Multiset.Filter
import Mathlib.Logic.Equiv.Basic

/-! Equal actual finite multisets of labels construct a label-preserving
bijection. Multiplicities are retained by matching the actual fibres.
This will match cycles with the same length and coefficient product. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.FiniteMultisetLabelMatching
variable {A B T : Type*} [Fintype A] [Fintype B]

def labelMultiset (f : A → T) : Multiset T := Finset.univ.val.map f

theorem count_labelMultiset (f : A → T) (t : T) :
    (labelMultiset f).count t=Fintype.card {a : A // f a=t} := by
  rw [labelMultiset,Multiset.count_map,Fintype.card_subtype]
  change (Finset.univ.val.filter (fun a => t=f a)).card=
    (Finset.univ.filter (fun a => f a=t)).val.card
  rw [Finset.filter_val]
  simp only [eq_comm]

theorem fibre_card_eq_of_labels_eq (f : A → T) (g : B → T)
    (h : labelMultiset f=labelMultiset g) (t : T) :
    Fintype.card {a : A // f a=t}=Fintype.card {b : B // g b=t} := by
  have hc := congrArg (fun s : Multiset T => s.count t) h
  simpa only [count_labelMultiset] using hc

def matchingEquiv (f : A → T) (g : B → T)
    (h : labelMultiset f=labelMultiset g) : A ≃ B :=
  Equiv.ofFiberEquiv (fun t =>
    Fintype.equivOfCardEq (fibre_card_eq_of_labels_eq f g h t))

theorem matchingEquiv_spec (f : A → T) (g : B → T)
    (h : labelMultiset f=labelMultiset g) (a : A) :
    g (matchingEquiv f g h a)=f a :=
  Equiv.ofFiberEquiv_map _ a

end SymmetricSubgroupAsymptotics.FiniteMultisetLabelMatching
