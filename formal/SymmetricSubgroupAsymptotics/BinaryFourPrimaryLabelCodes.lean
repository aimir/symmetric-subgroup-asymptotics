import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Multiset.MapFold
import Mathlib.Tactic.IntervalCases

/-! A bounded coefficient-label code for binary primary degree four.
The seven labels have degrees1,2,3,3,4,4,4; exponent slots are1..4.
Only weighted multisets are enumerated, never matrices, group elements
or permutation actions. Actual irreducible-label membership is a
separate theorem and is not an input to this finite count. -/
set_option autoImplicit false
set_option Elab.async false
namespace SymmetricSubgroupAsymptotics.BinaryFourPrimaryLabelCodes

abbrev Label := Fin 7 × Fin 4

def degree (i : Fin 7) : ℕ :=
  match i.val with
  | 0 => 1
  | 1 => 2
  | 2 => 3
  | 3 => 3
  | _ => 4

def labelWeight (a : Label) : ℕ := degree a.1*(a.2.val+1)

theorem labelWeight_pos (a : Label) : 0<labelWeight a := by
  have hd : 0<degree a.1 := by
    obtain ⟨i,hi⟩ := a.1
    interval_cases i <;> simp [degree]
  exact Nat.mul_pos hd (by omega)

def weight (m : Multiset Label) : ℕ := (m.map labelWeight).sum

def codes : ℕ → Finset (Multiset Label)
  | 0 => {0}
  | n+1 => (Finset.univ : Finset Label).biUnion (fun a =>
      if h : labelWeight a ≤ n+1 then
        (codes (n+1-labelWeight a)).image (fun m => a ::ₘ m)
      else ∅)
termination_by n => n
decreasing_by
  have hp := labelWeight_pos a
  omega

theorem mem_codes_weight (m : Multiset Label) : m∈codes (weight m) := by
  induction m using Multiset.induction_on with
  | empty => simp [weight,codes]
  | @cons a m ih =>
    have hp := labelWeight_pos a
    have hw : weight (a ::ₘ m)=labelWeight a+weight m := by
      simp only [weight,Multiset.map_cons,Multiset.sum_cons]
    have he : weight (a ::ₘ m)=(labelWeight a+weight m-1)+1 := by omega
    rw [he,codes]
    apply Finset.mem_biUnion.mpr
    refine ⟨a,Finset.mem_univ _,?_⟩
    have hle : labelWeight a≤(labelWeight a+weight m-1)+1 := by omega
    rw [dif_pos hle]
    apply Finset.mem_image.mpr
    refine ⟨m,?_,rfl⟩
    simpa only [show (labelWeight a+weight m-1)+1-labelWeight a=weight m by omega] using ih

theorem card_codes_four : (codes 4).card=14 := by decide +kernel

end SymmetricSubgroupAsymptotics.BinaryFourPrimaryLabelCodes
