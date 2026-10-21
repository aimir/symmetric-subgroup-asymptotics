import SymmetricSubgroupAsymptotics.FiniteRowLeadingWeight
import Mathlib.Data.Fin.Tuple.Basic

/-! Leading terms in two ordered layers. Every upper index is above
every lower index, so unrestricted lower-layer errors do not affect an
upper leading term. -/
set_option autoImplicit false
namespace SymmetricSubgroupAsymptotics.TwoLayerLeadingTerms

variable {k : Type} [AddCommGroup k] {n : ℕ}

theorem upper_iff (z s : Fin n → k) (a : Fin n) :
    FiniteRowLeadingWeight.HasLeading (Fin.append z s) (Fin.natAdd n a) ↔
      FiniteRowLeadingWeight.HasLeading s a := by
  constructor
  · intro hv
    refine ⟨by simpa only [Fin.append_right] using hv.1, ?_⟩
    intro b hb
    have h : Fin.natAdd n a < Fin.natAdd n b := by
      change n + a.val < n + b.val
      omega
    simpa only [Fin.append_right] using hv.2 (Fin.natAdd n b) h
  · intro hv
    refine ⟨by simpa only [Fin.append_right] using hv.1, ?_⟩
    intro b
    refine Fin.addCases (fun j hj => ?_) (fun j hj => ?_) b
    · change n + a.val < j.val at hj
      have h := j.isLt
      omega
    · have h : a < j := by
        change n + a.val < n + j.val at hj
        change a.val < j.val
        omega
      simpa only [Fin.append_right] using hv.2 j h

theorem lower_iff (z s : Fin n → k) (a : Fin n) :
    FiniteRowLeadingWeight.HasLeading (Fin.append z s) (Fin.castAdd n a) ↔
      FiniteRowLeadingWeight.HasLeading z a ∧ s = 0 := by
  constructor
  · intro hv
    refine ⟨⟨by simpa only [Fin.append_left] using hv.1, ?_⟩, ?_⟩
    · intro b hb
      have h : Fin.castAdd n a < Fin.castAdd n b := hb
      simpa only [Fin.append_left] using hv.2 (Fin.castAdd n b) h
    · funext b
      have h : Fin.castAdd n a < Fin.natAdd n b := by
        change a.val < n + b.val
        have ha := a.isLt
        omega
      simpa only [Fin.append_right] using hv.2 (Fin.natAdd n b) h
  · rintro ⟨hv, rfl⟩
    refine ⟨by simpa only [Fin.append_left] using hv.1, ?_⟩
    intro b
    refine Fin.addCases (fun j hj => ?_) (fun j _ => ?_) b
    · have h : a < j := hj
      simpa only [Fin.append_left] using hv.2 j h
    · simp only [Fin.append_right, Pi.zero_apply]

end SymmetricSubgroupAsymptotics.TwoLayerLeadingTerms
