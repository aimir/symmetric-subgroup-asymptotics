import SymmetricSubgroupAsymptotics.BinaryPairFrameOneSignKernel
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeThreeHighSignIdentitySource

/-!
# Exact high/low sign split after four ternary blocks

The literal sign fibres are equicardinal, so the number of realized signs
divides the number of blocks.  At the three surviving block counts this
leaves exactly the high-sign cases already closed by the cyclic-dual theorem
and the low-sign counts `1`, `1/2`, and `1/2/3`, respectively.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace BinaryPairFrame

variable {X I : Type*} {G : Subgroup (Equiv.Perm X)}
  (F : BinaryPairFrame G I)

/-- Arithmetic exhaustion of the sign-isotype counts at six, twelve, and
eighteen coordinates. -/
theorem coordinateSign_high_or_low_six_twelve_eighteen
    [Finite I] [Nonempty I]
    (htrans : MulAction.IsPretransitive G X)
    (hsize : Nat.card I = 6 ∨ Nat.card I = 12 ∨ Nat.card I = 18) :
    ((Nat.card I = 6 ∧ 2 ≤ Nat.card (CoordinateSign F)) ∨
      (Nat.card I = 12 ∧ 3 ≤ Nat.card (CoordinateSign F)) ∨
      (Nat.card I = 18 ∧ 6 ≤ Nat.card (CoordinateSign F))) ∨
    ((Nat.card I = 6 ∧ Nat.card (CoordinateSign F) = 1) ∨
      (Nat.card I = 12 ∧
        (Nat.card (CoordinateSign F) = 1 ∨
          Nat.card (CoordinateSign F) = 2)) ∨
      (Nat.card I = 18 ∧
        (Nat.card (CoordinateSign F) = 1 ∨
          Nat.card (CoordinateSign F) = 2 ∨
          Nat.card (CoordinateSign F) = 3))) := by
  let i0 : I := Classical.choice inferInstance
  let q := Nat.card (CoordinateSign F)
  let m := Nat.card {i : I // coordinateSign F i = coordinateSign F i0}
  have hproduct : q * m = Nat.card I := by
    exact coordinateSign_count_mul_fibre_card F htrans i0
  have hqpos : 0 < q := Nat.card_pos_iff.mpr
    ⟨⟨coordinateSign F i0⟩, inferInstance⟩
  rcases hsize with hsix | htwelve | heighteen
  · by_cases hhigh : 2 ≤ q
    · exact Or.inl (Or.inl ⟨hsix, hhigh⟩)
    · exact Or.inr (Or.inl ⟨hsix, by omega⟩)
  · by_cases hhigh : 3 ≤ q
    · exact Or.inl (Or.inr (Or.inl ⟨htwelve, hhigh⟩))
    · exact Or.inr (Or.inr (Or.inl ⟨htwelve, by omega⟩))
  · by_cases hhigh : 6 ≤ q
    · exact Or.inl (Or.inr (Or.inr ⟨heighteen, hhigh⟩))
    · have hqm : q * m = 18 := by simpa only [heighteen] using hproduct
      have hqdvd : q ∣ 18 := ⟨m, hqm.symm⟩
      have hlow : q = 1 ∨ q = 2 ∨ q = 3 := by
        interval_cases q <;> norm_num at hqdvd ⊢
      exact Or.inr (Or.inr (Or.inr ⟨heighteen, hlow⟩))

end BinaryPairFrame

namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer

variable {w : ℕ} {U : PreE7NonPairActionClass w}
  {basePoint : Fin w}
  (block : OriginalMinimalBlock
    (A := preE7NonPairAction w U) basePoint)
  (P : PrimitiveAffineProfile block.Component block.Fibre)
  [Nontrivial block.Fibre]

/-- Apply the exact sign-count exhaustion directly to the literal
degree-three signed quotient frame. -/
theorem degreeThreePostFour_highSign_or_lowSign
    (hr : Nat.card block.Fibre = 3)
    (hcomponent : Nat.card block.Component = 6)
    (hs : Nat.card block.Points = 6 ∨
      Nat.card block.Points = 12 ∨ Nat.card block.Points = 18) :
    ((Nat.card block.Points = 6 ∧
        2 ≤ Nat.card (BinaryPairFrame.CoordinateSign
          (degreeThreeSignedQuotientPairFrame block P hr))) ∨
      (Nat.card block.Points = 12 ∧
        3 ≤ Nat.card (BinaryPairFrame.CoordinateSign
          (degreeThreeSignedQuotientPairFrame block P hr))) ∨
      (Nat.card block.Points = 18 ∧
        6 ≤ Nat.card (BinaryPairFrame.CoordinateSign
          (degreeThreeSignedQuotientPairFrame block P hr)))) ∨
    ((Nat.card block.Points = 6 ∧
        Nat.card (BinaryPairFrame.CoordinateSign
          (degreeThreeSignedQuotientPairFrame block P hr)) = 1) ∨
      (Nat.card block.Points = 12 ∧
        (Nat.card (BinaryPairFrame.CoordinateSign
            (degreeThreeSignedQuotientPairFrame block P hr)) = 1 ∨
          Nat.card (BinaryPairFrame.CoordinateSign
            (degreeThreeSignedQuotientPairFrame block P hr)) = 2)) ∨
      (Nat.card block.Points = 18 ∧
        (Nat.card (BinaryPairFrame.CoordinateSign
            (degreeThreeSignedQuotientPairFrame block P hr)) = 1 ∨
          Nat.card (BinaryPairFrame.CoordinateSign
            (degreeThreeSignedQuotientPairFrame block P hr)) = 2 ∨
          Nat.card (BinaryPairFrame.CoordinateSign
            (degreeThreeSignedQuotientPairFrame block P hr)) = 3))) := by
  let F := degreeThreeSignedQuotientPairFrame block P hr
  have htrans := degreeThreeSignedQuotientRange_pretransitive
    block P hr hcomponent
  exact BinaryPairFrame.coordinateSign_high_or_low_six_twelve_eighteen
    F htrans hs

end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
