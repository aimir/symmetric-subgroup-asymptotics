import SymmetricSubgroupAsymptotics.CFSGTwistedADerivedFaithfulness

/-! Arbitrary-rank endpoint for the SAME original twisted-A model.
The source's own simplicity instance is the only descent assumption.
The natural derived image is recognized projectively, not identified by
name with a full unitary group. Rank two remains a separate source seam. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGTwistedANaturalMatrices

universe u

private def fromThreeFamily {F : ℕ → Sort u} (f : ∀ s, F (s + 3))
    (r : ℕ) (hr : 3 ≤ r) : F r := by
  cases r with
  | zero => exact False.elim (by omega)
  | succ r =>
    cases r with
    | zero => exact False.elim (by omega)
    | succ r =>
      cases r with
      | zero => exact False.elim (by omega)
      | succ s => exact f s

theorem derived_natural_projective_nontrivial_of_three_le (r : ℕ) (hr : 3 ≤ r)
    (q : CFSG.PrimePower) :
    Nontrivial ((twistedDerivedAction r q).range ⧸
      Subgroup.center (twistedDerivedAction r q).range) := by
  obtain ⟨s, hs⟩ := Nat.exists_eq_add_of_le hr
  have he : r = s + 3 := by omega
  clear hs
  subst r
  exact derived_natural_projective_nontrivial s q

def twistedA_natural_projective_equiv_of_three_le (r : ℕ) (hr : 3 ≤ r)
    (q : CFSG.PrimePower) [hsimple : IsSimpleGroup (CFSG.Models.TwistedA r q)] :
    CFSG.Models.TwistedA r q ≃*
      ((twistedDerivedAction r q).range ⧸ Subgroup.center (twistedDerivedAction r q).range) := by
  exact fromThreeFamily
    (F := fun n => IsSimpleGroup (CFSG.Models.TwistedA n q) →
      (CFSG.Models.TwistedA n q ≃*
        ((twistedDerivedAction n q).range ⧸ Subgroup.center (twistedDerivedAction n q).range)))
    (fun s hs => @twistedA_natural_projective_equiv s q hs) r hr hsimple

end SymmetricSubgroupAsymptotics.CFSGTwistedANaturalMatrices
