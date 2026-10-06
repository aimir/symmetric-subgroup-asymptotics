import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeThreeLocalScalar
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeThreeSignedQuotientPairFrame
import SymmetricSubgroupAsymptotics.OddMarkerTernaryChart

/-!
# The two-point bit and the local ternary scalar

The compressed complement of a degree-three affine component acts on the
two nonidentity translations.  Its displacement of bit zero is therefore a
literal binary coordinate.  This file proves that the same element acts on
the one-dimensional ternary translation module by the corresponding sign
scalar.

The proof uses only the faithful local representation, its one-dimensional
scalar compression, and the actual two-point action.  No classification of
the ambient four-block action enters.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer

open OddMarkerTernaryChart

variable {w : ℕ} {U : PreE7NonPairActionClass w}
  {basePoint : Fin w}
  (block : OriginalMinimalBlock
    (A := preE7NonPairAction w U) basePoint)
  (P : PrimitiveAffineProfile block.Component block.Fibre)
  [Nontrivial block.Fibre]

/-- Displacement of bit zero under one literal local-complement element. -/
def degreeThreeLocalBit
    (hr : Nat.card block.Fibre = 3)
    (q : LocalQuotient block P) : ZMod 2 :=
  (degreeThreeBitEquiv block hr).symm
    (q.1 (degreeThreeBitEquiv block hr 0))

omit [Nontrivial block.Fibre] in
/-- Every literal local-complement permutation is translation by its
retained bit. -/
theorem degreeThreeLocalBit_action
    (hr : Nat.card block.Fibre = 3)
    (q : LocalQuotient block P) (b : ZMod 2) :
    (degreeThreeBitEquiv block hr).symm
        (q.1 (degreeThreeBitEquiv block hr b)) =
      b + degreeThreeLocalBit block P hr q := by
  exact binary_injective_translate
    (fun x => (degreeThreeBitEquiv block hr).symm
      (q.1 (degreeThreeBitEquiv block hr x)))
    ((degreeThreeBitEquiv block hr).symm.injective.comp
      (q.1.injective.comp
        (degreeThreeBitEquiv block hr).injective))
    b

omit [Nontrivial block.Fibre] in
/-- The local bit vanishes exactly on the identity complement element. -/
theorem degreeThreeLocalBit_eq_zero_iff
    (hr : Nat.card block.Fibre = 3)
    (q : LocalQuotient block P) :
    degreeThreeLocalBit block P hr q = 0 ↔ q = 1 := by
  constructor
  · intro hbit
    apply Subtype.ext
    apply Equiv.ext
    intro x
    obtain ⟨b, rfl⟩ := (degreeThreeBitEquiv block hr).surjective x
    apply (degreeThreeBitEquiv block hr).symm.injective
    rw [degreeThreeLocalBit_action block P hr q b, hbit, add_zero]
    rw [show (1 : LocalQuotient block P).1 =
      (1 : Equiv.Perm (Fin (localDegree block))) from rfl]
    exact (degreeThreeBitEquiv block hr).symm_apply_apply b |>.symm
  · rintro rfl
    change (degreeThreeBitEquiv block hr).symm
      ((1 : LocalQuotient block P).1 (degreeThreeBitEquiv block hr 0)) = 0
    rw [show (1 : LocalQuotient block P).1 =
      (1 : Equiv.Perm (Fin (localDegree block))) from rfl]
    exact (degreeThreeBitEquiv block hr).symm_apply_apply 0

/-- A local scalar cannot vanish because it represents an invertible linear
map on a nonzero one-dimensional module. -/
theorem degreeThreeLocalScalar_ne_zero
    (hr : Nat.card block.Fibre = 3)
    (q : LocalQuotient block P) :
    degreeThreeLocalScalar block P hr q ≠ 0 := by
  letI : Fact P.p.Prime := (chart block P).primeFact
  have hdim : Module.finrank (ZMod P.p) (chart block P).V = 1 := by
    have hdim' := (degreeThree_translation_prime_dim block P hr).2
    change Module.finrank (ZMod P.p) (chart block P).V = 1 at hdim'
    exact hdim'
  letI : Nontrivial (chart block P).V :=
    Module.nontrivial_of_finrank_pos (R := ZMod P.p) (by
      rw [hdim]
      decide)
  obtain ⟨v, hv⟩ := exists_ne (0 : (chart block P).V)
  intro hzero
  have hinj :=
    ((binaryAffineLocalLinearRepresentation block P).ρ.apply_bijective q).1
  apply hv
  apply hinj
  rw [degreeThreeLocalScalar_action block P hr q v, hzero, zero_smul]
  simp

/-- The scalar representation and the retained two-point bit carry the same
sign, transported across the forced equality of the local field with
`F₃`. -/
theorem degreeThreeLocalScalar_eq_signScalar
    (hr : Nat.card block.Fibre = 3)
    (q : LocalQuotient block P) :
    degreeThreeScalarFieldEquiv block P hr
        (degreeThreeLocalScalar block P hr q) =
      signScalar (Multiplicative.ofAdd
        (degreeThreeLocalBit block P hr q)) := by
  have hbit : degreeThreeLocalBit block P hr q = 0 ∨
      degreeThreeLocalBit block P hr q = 1 := by
    have hbits : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by decide +kernel
    exact hbits _
  rcases hbit with hbit | hbit
  · have hq : q = 1 :=
      (degreeThreeLocalBit_eq_zero_iff block P hr q).mp hbit
    subst q
    rw [degreeThreeLocalScalar_one, map_one, hbit]
    exact OddMarkerTernaryChart.signScalar_one.symm
  · let e := degreeThreeScalarFieldEquiv block P hr
    have hscalar0 : degreeThreeLocalScalar block P hr q ≠ 0 :=
      degreeThreeLocalScalar_ne_zero block P hr q
    have hqne : q ≠ 1 := by
      intro hq
      have := (degreeThreeLocalBit_eq_zero_iff block P hr q).2 hq
      rw [hbit] at this
      norm_num at this
    have hscalar1 : degreeThreeLocalScalar block P hr q ≠ 1 := by
      intro hone
      apply hqne
      apply degreeThreeLocalScalar_injective block P hr
      simpa only [degreeThreeLocalScalar_one] using hone
    have hthree : ∀ z : ZMod 3, z = 0 ∨ z = 1 ∨ z = -1 := by
      decide +kernel
    rcases hthree (e (degreeThreeLocalScalar block P hr q)) with
      hzero | hone | hneg
    · exact False.elim (hscalar0 (e.injective (by simpa [e] using hzero)))
    · exact False.elim (hscalar1 (e.injective (by simpa [e] using hone)))
    · rw [hbit, signScalar_nontrivial]
      exact hneg

end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
