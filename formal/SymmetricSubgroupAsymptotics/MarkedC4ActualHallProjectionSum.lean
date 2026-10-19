import SymmetricSubgroupAsymptotics.MarkedC4ActualProjectionHallFibre
import SymmetricSubgroupAsymptotics.MarkedC4ActualHallColumnCompression
import Mathlib.Data.SetLike.Fintype

/-! Correlated Hall summation over actual retained physical images.
The source is the actual second projection of each subgroup. The SINGLE
mark group occurs only in the first factor; it is never copied per row.
The projection and recovery construct the injection, without an encoding
or enumeration callback. -/
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators
namespace SymmetricSubgroupAsymptotics.MarkedC4.ActualHallProjectionSum
open AbelianProductGraphClassification

variable {A B M : Type} [CommGroup A] [Group B] [Group M]
  (P : Subgroup B → Prop)

abbrev Source := {E : Subgroup B // P E}
abbrev Family := {H : Subgroup ((A × M) × B) //
  P (H.map (MonoidHom.snd (A × M) B))}

local instance [Finite B] : Fintype (Source P) := Fintype.ofFinite _

def code (H : Family (A := A) (M := M) P) :
    Σ E : Source P,FullSecond (A × M) E.val :=
  ⟨⟨H.val.map (MonoidHom.snd (A × M) B),H.property⟩,
    ActualProjectionHallFibre.code _ ⟨H.val,rfl⟩⟩

def recover (z : Σ E : Source P,FullSecond (A × M) E.val) :
    Subgroup ((A × M) × B) :=
  z.2.val.map (ActualProjectionHallFibre.inclusion z.1.val)

theorem recover_code (H : Family (A := A) (M := M) P) :
    recover P (code P H)=H.val :=
  ActualProjectionHallFibre.recover _ ⟨H.val,rfl⟩

theorem code_injective : Function.Injective (@code A B M _ _ _ P) := by
  intro H K he
  apply Subtype.ext
  exact (recover_code P H).symm.trans
    ((congrArg (recover P) he).trans (recover_code P K))

/-- Actual Hall fibres are summed over the SAME physical second images.
Any literal normal-tableau restriction may be used for P. -/
theorem card_le_sum [Finite A] [Finite B] [Finite M] :
    Nat.card (Family (A := A) (M := M) P) ≤
      ∑ E : Source P,Nat.card (FullSecond (A × M) E.val) := by
  have h := Nat.card_le_card_of_injective (code (A := A) (M := M) P)
    (code_injective (A := A) (M := M) P)
  simpa only [Nat.card_sigma] using h

/-- The complete correlated two-column Hall sum for the actual family.
Both columns inside each summand belong to its actual E; no independent
maximum of the two source types is taken. -/
theorem cyclicFour_card_le_sum (m r : ℕ) [Finite A] [Finite B]
    (hA : HasExp2 A (2+m)) {a : ℝ}
    (hcard : (Nat.card A : ℝ)≤(2 : ℝ)^(a/2)) :
    (Nat.card (Family (A := A) (M := Multiplicative (Fin r → ZMod 4)) P) : ℝ) ≤
      ∑ E : Source P,
        ((∏ k ∈ Finset.range (2+m),
          ((col (A × Multiplicative (Fin r → ZMod 4)) k : ℝ)+1))*4^(2+m))*
        (2 : ℝ)^(psi (a/2+r) (col (Abelianization E.val) 0)+
          psi r (col (Abelianization E.val) 1)) := by
  letI : Fintype (Subgroup (A × Multiplicative (Fin r → ZMod 4))) := Fintype.ofFinite _
  calc
    (Nat.card (Family (A := A) (M := Multiplicative (Fin r → ZMod 4)) P) : ℝ) ≤
        ∑ E : Source P,(Nat.card (FullSecond
          (A × Multiplicative (Fin r → ZMod 4)) E.val) : ℝ) := by
      exact_mod_cast card_le_sum (A := A) (M := Multiplicative (Fin r → ZMod 4)) P
    _ ≤ _ := Finset.sum_le_sum (fun E _ =>
      ActualHallColumnCompression.fullSecond_le m r A hA E.val hcard)

end SymmetricSubgroupAsymptotics.MarkedC4.ActualHallProjectionSum
