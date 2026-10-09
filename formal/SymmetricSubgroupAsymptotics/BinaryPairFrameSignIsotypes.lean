import SymmetricSubgroupAsymptotics.BinaryPairFrameTransport
import SymmetricSubgroupAsymptotics.BinaryPairFrameEquivariance

/-!
# Sign isotypes of an arbitrary literal binary pair frame

The pair-kernel bit at one coordinate is an actual character of the
literal kernel.  Equality of these characters is preserved and reflected
by the top action.  Hence a transitive pair frame has equally sized sign
fibres, and the number of occurring characters times their common
multiplicity is the original number of pairs.

This generic form is used at six and twelve blocks.  It is the same
literal construction previously specialized to the four-block split.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace BinaryPairFrame

variable {X I : Type} {G : Subgroup (Equiv.Perm X)}

/-- The actual bit character carried by one pair coordinate. -/
def coordinateSignFunction
    (F : BinaryPairFrame G I) (i : I) : F.top.ker → ZMod 2 :=
  fun k => F.bits k i

/-- The finite set of bit characters which really occur in the frame. -/
def CoordinateSign (F : BinaryPairFrame G I) : Type :=
  Set.range (coordinateSignFunction F)

/-- The sign label of a literal pair coordinate. -/
def coordinateSign
    (F : BinaryPairFrame G I) (i : I) : CoordinateSign F :=
  ⟨coordinateSignFunction F i, i, rfl⟩

theorem coordinateSign_surjective
    (F : BinaryPairFrame G I) :
    Function.Surjective (coordinateSign F) := by
  rintro ⟨chi, i, rfl⟩
  exact ⟨i, rfl⟩

noncomputable instance coordinateSign_finite
    [Finite I] (F : BinaryPairFrame G I) : Finite (CoordinateSign F) :=
  Finite.of_surjective (coordinateSign F) (coordinateSign_surjective F)

private theorem coordinateSignFunction_top
    (F : BinaryPairFrame G I) (u : G) (i : I) :
    coordinateSignFunction F (F.top u i) =
      fun k => coordinateSignFunction F i (MulAut.conjNormal u⁻¹ k) := by
  funext k
  simpa only [coordinateSignFunction, map_inv, inv_inv] using
    (F.bits_conjNormal u⁻¹ k i).symm

private theorem coordinateSign_top_imp
    (F : BinaryPairFrame G I) (u : G) (i j : I)
    (h : coordinateSign F i = coordinateSign F j) :
    coordinateSign F (F.top u i) = coordinateSign F (F.top u j) := by
  apply Subtype.ext
  change coordinateSignFunction F (F.top u i) =
    coordinateSignFunction F (F.top u j)
  rw [coordinateSignFunction_top F, coordinateSignFunction_top F]
  exact congrArg
    (fun f : F.top.ker → ZMod 2 =>
      fun k => f (MulAut.conjNormal u⁻¹ k))
    (congrArg Subtype.val h)

/-- The actual top action preserves and reflects equality of literal sign
characters. -/
theorem coordinateSign_top_eq_iff
    (F : BinaryPairFrame G I) (u : G) (i j : I) :
    coordinateSign F (F.top u i) = coordinateSign F (F.top u j) ↔
      coordinateSign F i = coordinateSign F j := by
  constructor
  · intro h
    have h' := coordinateSign_top_imp F u⁻¹
      (F.top u i) (F.top u j) h
    simpa using h'
  · exact coordinateSign_top_imp F u i j

/-- A top element gives an equivalence between the corresponding literal
sign fibres. -/
def coordinateSignFiberEquiv
    (F : BinaryPairFrame G I) (u : G) (i : I) :
    {j : I // coordinateSign F j = coordinateSign F i} ≃
      {j : I // coordinateSign F j = coordinateSign F (F.top u i)} where
  toFun j := ⟨F.top u j,
    (coordinateSign_top_eq_iff F u j.1 i).2 j.2⟩
  invFun j := ⟨(F.top u)⁻¹ j,
    (coordinateSign_top_eq_iff F u ((F.top u)⁻¹ j.1) i).1 (by
      simpa using j.2)⟩
  left_inv j := by
    apply Subtype.ext
    exact (F.top u).symm_apply_apply j
  right_inv j := by
    apply Subtype.ext
    exact (F.top u).apply_symm_apply j

/-- Transitivity on the physical pair action makes all occurring sign
fibres equicardinal. -/
theorem coordinateSign_fibre_card_eq
    [Finite I] (F : BinaryPairFrame G I)
    (htrans : MulAction.IsPretransitive G X)
    (chi psi : CoordinateSign F) :
    Nat.card {i : I // coordinateSign F i = chi} =
      Nat.card {i : I // coordinateSign F i = psi} := by
  obtain ⟨i, rfl⟩ := coordinateSign_surjective F chi
  obtain ⟨j, rfl⟩ := coordinateSign_surjective F psi
  letI : MulAction.IsPretransitive G X := htrans
  letI : MulAction.IsPretransitive F.top.range I := F.top_pretransitive
  obtain ⟨t, ht⟩ := MulAction.exists_smul_eq F.top.range i j
  obtain ⟨u, rfl⟩ := F.top.rangeRestrict_surjective t
  have htop : F.top u i = j := by simpa using ht
  simpa only [htop] using
    Nat.card_congr (coordinateSignFiberEquiv F u i)

attribute [local instance] Fintype.ofFinite

/-- Exact orbit partition formula for the literal sign characters. -/
theorem coordinateSign_count_mul_fibre_card
    [Finite I] [Nonempty I]
    (F : BinaryPairFrame G I)
    (htrans : MulAction.IsPretransitive G X)
    (i0 : I) :
    Nat.card (CoordinateSign F) *
        Nat.card {i : I // coordinateSign F i = coordinateSign F i0} =
      Nat.card I := by
  let m := Nat.card {i : I //
    coordinateSign F i = coordinateSign F i0}
  calc
    Nat.card (CoordinateSign F) * m =
        ∑ _chi : CoordinateSign F, m := by
      simp only [Finset.sum_const, nsmul_eq_mul, Finset.card_univ,
        Fintype.card_eq_nat_card, Nat.cast_id]
    _ = ∑ chi : CoordinateSign F,
        Nat.card {i : I // coordinateSign F i = chi} := by
      apply Finset.sum_congr rfl
      intro chi _hchi
      exact (coordinateSign_fibre_card_eq F htrans chi
        (coordinateSign F i0)).symm
    _ = Nat.card (Sigma fun chi : CoordinateSign F =>
        {i : I // coordinateSign F i = chi}) := Nat.card_sigma.symm
    _ = Nat.card I :=
      Nat.card_congr (Equiv.sigmaFiberEquiv (coordinateSign F))

/-- At six coordinates, at least two sign classes force one isotype to
have size one, two, or three. -/
theorem coordinateSign_fibre_card_cases_six
    [Finite I] [Nonempty I]
    (F : BinaryPairFrame G I)
    (htrans : MulAction.IsPretransitive G X)
    (hsix : Nat.card I = 6)
    (htwo : 2 ≤ Nat.card (CoordinateSign F))
    (i0 : I) :
    Nat.card {i : I // coordinateSign F i = coordinateSign F i0} = 1 ∨
      Nat.card {i : I // coordinateSign F i = coordinateSign F i0} = 2 ∨
      Nat.card {i : I // coordinateSign F i = coordinateSign F i0} = 3 := by
  have hproduct := coordinateSign_count_mul_fibre_card F htrans i0
  rw [hsix] at hproduct
  have hmpos : 0 < Nat.card {i : I //
      coordinateSign F i = coordinateSign F i0} :=
    Nat.card_pos_iff.mpr ⟨⟨⟨i0, rfl⟩⟩, inferInstance⟩
  omega

/-- At twelve coordinates, at least three sign classes force one isotype
to have size one, two, three, or four. -/
theorem coordinateSign_fibre_card_cases_twelve
    [Finite I] [Nonempty I]
    (F : BinaryPairFrame G I)
    (htrans : MulAction.IsPretransitive G X)
    (htwelve : Nat.card I = 12)
    (hthree : 3 ≤ Nat.card (CoordinateSign F))
    (i0 : I) :
    Nat.card {i : I // coordinateSign F i = coordinateSign F i0} = 1 ∨
      Nat.card {i : I // coordinateSign F i = coordinateSign F i0} = 2 ∨
      Nat.card {i : I // coordinateSign F i = coordinateSign F i0} = 3 ∨
      Nat.card {i : I // coordinateSign F i = coordinateSign F i0} = 4 := by
  have hproduct := coordinateSign_count_mul_fibre_card F htrans i0
  rw [htwelve] at hproduct
  have hmpos : 0 < Nat.card {i : I //
      coordinateSign F i = coordinateSign F i0} :=
    Nat.card_pos_iff.mpr ⟨⟨⟨i0, rfl⟩⟩, inferInstance⟩
  omega

/-- At eighteen coordinates, at least six sign classes force every
isotype to have size one, two, or three. -/
theorem coordinateSign_fibre_card_cases_eighteen
    [Finite I] [Nonempty I]
    (F : BinaryPairFrame G I)
    (htrans : MulAction.IsPretransitive G X)
    (heighteen : Nat.card I = 18)
    (hsix : 6 ≤ Nat.card (CoordinateSign F))
    (i0 : I) :
    Nat.card {i : I // coordinateSign F i = coordinateSign F i0} = 1 ∨
      Nat.card {i : I // coordinateSign F i = coordinateSign F i0} = 2 ∨
      Nat.card {i : I // coordinateSign F i = coordinateSign F i0} = 3 := by
  have hproduct := coordinateSign_count_mul_fibre_card F htrans i0
  rw [heighteen] at hproduct
  have hmpos : 0 < Nat.card {i : I //
      coordinateSign F i = coordinateSign F i0} :=
    Nat.card_pos_iff.mpr ⟨⟨⟨i0, rfl⟩⟩, inferInstance⟩
  omega

end BinaryPairFrame
end SymmetricSubgroupAsymptotics

end
