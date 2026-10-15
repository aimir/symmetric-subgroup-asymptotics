import SymmetricSubgroupAsymptotics.BinaryPlaneKernelClassification
import SymmetricSubgroupAsymptotics.PrimitiveAffineZeroCoreCoinducedConsumer
import SymmetricSubgroupAsymptotics.BinaryPairSixteenFrameBound
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameLocalRepresentation

/-!
The nontrivial pair-kernel structural branch, returned to the original
degree-four profile. The only finite inputs are the rank and local-frame
checks on the actual eight-pair quotient. The top rank six, original frame
head four, exact local extension, and original-profile transport are proved.
This module does not assume or assert that every sixteen-point top has pairs.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SymmetricSubgroupAsymptotics

namespace BinaryPairFrame

variable {p : ℕ} [Fact p.Prime]
  {X I C V : Type} {U : Subgroup (Equiv.Perm X)}
  [Finite X] [Finite I] [Group C] [Finite C]
  [AddCommGroup V] [Module (ZMod p) V] [FiniteDimensional (ZMod p) V]
  (F : BinaryPairFrame U I) [MulAction.IsPretransitive U X]

/-- Characteristic transport is performed before substituting an affine
profile, so it does not alter any of that profile's dependent original data. -/
theorem originalFrame_head_le_four_at
    (hp : p = 2) (hker : F.top.ker ≠ ⊥) (i : I)
    (f : F.pointStabilizer i →* C) (hf : Function.Surjective f)
    (hC : Nat.card C = 3 ∨ (Nat.card C = 6 ∧ ¬ IsMulCommutative C))
    (tau : Representation (ZMod p) C V)
    (hquotient : ∀ A : Subrepresentation
      (Representation.coind (F.pairTopStabilizer i).subtype
        (tau.comp (F.descendedPointLocalMap hker i f hf hC))),
      Module.finrank (ZMod p)
        (A.toRepresentation.IntertwiningMap
          (Representation.trivial (ZMod p) F.top.range (ZMod p))) ≤ 2)
    (B : Subrepresentation
      (Representation.coind (F.pointStabilizer i).subtype (tau.comp f))) :
    Module.finrank (ZMod p)
      (B.toRepresentation.IntertwiningMap
        (Representation.trivial (ZMod p) U (ZMod p))) ≤ 4 := by
  subst p
  exact F.originalFrame_head_le_four hker i f hf hC tau hquotient B

end BinaryPairFrame

namespace Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer

variable {w : ℕ} {U : PreE7NonPairActionClass w} {basePoint : Fin w}
  (block : OriginalMinimalBlock (A := preE7NonPairAction w U) basePoint)
  (P : PrimitiveAffineProfile block.Component block.Fibre)
  [Nontrivial block.Fibre]

local instance : Fact P.p.Prime := (chart block P).primeFact

/-- The actual local target has no nontrivial normal binary subgroup. -/
theorem degreeFourLocalTarget_eligible (hr : Nat.card block.Fibre = 4) :
    Nat.card (LocalQuotient block P) = 3 ∨
      (Nat.card (LocalQuotient block P) = 6 ∧
        ¬ IsMulCommutative (LocalQuotient block P)) := by
  rcases degreeFourZeroCoreTopStabilizerLocalTarget_card block P hr with h3 | h6
  · exact Or.inl h3
  · refine Or.inr ⟨h6, ?_⟩
    have hdim : Module.finrank (ZMod P.p) (chart block P).V = 2 := by
      change (chart block P).d = 2
      exact (degreeFour_translationDimension block P hr).2
    exact BinaryPlaneKernelClassification.not_commutative_of_card_six_at
      (degreeFour_profilePrime_eq_two block P hr)
      (binaryAffineLocalLinearRepresentation block P).ρ h6 hdim
      (binaryAffineLocalLinearRepresentation_injective block P)

local instance : MulAction.IsPretransitive block.Top block.Points := block.top_pretransitive

/-- The actual point-stabilizer map used in the pair branch. -/
abbrev degreeFourPairPointLocalMap
    (hr : Nat.card block.Fibre = 4) (hD : degreeFourTernaryCore block P = ⊥)
    {I : Type} (F : BinaryPairFrame block.Top I) (i : I) :
    F.pointStabilizer i →* LocalQuotient block P :=
  degreeFourZeroCoreTopStabilizerLocalMap block P hr hD (F.frame (i, 0))

/-- The exact descended local representation of the eight-pair quotient. -/
abbrev degreeFourPairQuotientLocalRepresentation
    (hr : Nat.card block.Fibre = 4) (hD : degreeFourTernaryCore block P = ⊥)
    {I : Type} (F : BinaryPairFrame block.Top I) (hker : F.top.ker ≠ ⊥) (i : I) :
    Representation (ZMod P.p) (F.pairTopStabilizer i) (chart block P).V :=
  (binaryAffineLocalLinearRepresentation block P).ρ.comp
    (F.descendedPointLocalMap hker i (degreeFourPairPointLocalMap block P hr hD F i)
      (degreeFourZeroCoreTopStabilizerLocalMap_surjective block P hr hD (F.frame (i, 0)))
      (degreeFourLocalTarget_eligible block P hr))

/-- The complete nontrivial-pair-kernel structural consumer. Its finite
obligations are on the actual eight-pair top and its descended local map. -/
def degreeFourZeroCoreSixteenPairKernelNontrivialBounds
    (hr : Nat.card block.Fibre = 4) (hD : degreeFourTernaryCore block P = ⊥)
    {I : Type} [Finite I] (F : BinaryPairFrame block.Top I)
    (hker : F.top.ker ≠ ⊥) (hcard : Nat.card I = 8) (i : I)
    (htop : ∀ (N : Subgroup F.top.range) [N.Normal],
      Module.finrank (ZMod 2) (primeRelativeCharacters 2 N) ≤ 2)
    (hframe : ∀ B : Subrepresentation
      (Representation.coind (F.pairTopStabilizer i).subtype
        (degreeFourPairQuotientLocalRepresentation block P hr hD F hker i)),
      Module.finrank (ZMod P.p)
        (B.toRepresentation.IntertwiningMap
          (Representation.trivial (ZMod P.p) F.top.range (ZMod P.p))) ≤ 2) :
    DegreeFourZeroCoreFiniteFrameBounds block P 10 := by
  letI : Nontrivial I := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  letI : MulAction block.Top I := MulAction.compHom I F.top
  letI : MulAction.IsPretransitive block.Top I := by
    constructor
    intro a b
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq block.Top (F.frame (a, 0)) (F.frame (b, 0))
    refine ⟨g, ?_⟩
    have h := F.intertwine g (a, 0)
    change (F.frame.symm (g • F.frame (a, 0))).1 = F.top g a at h
    rw [hg, Equiv.symm_apply_apply] at h
    exact h.symm
  apply DegreeFourZeroCoreFiniteFrameBounds.ofTopCoinduced block P hr hD
    (F.frame (i, 0)) 6 4 10 (by decide)
  · intro N _
    exact F.eightPair_relativeHead_le_six (fun _ _ => rfl) hcard htop N
  · intro B
    exact F.originalFrame_head_le_four_at (degreeFour_profilePrime_eq_two block P hr)
      hker i (degreeFourPairPointLocalMap block P hr hD F i)
      (degreeFourZeroCoreTopStabilizerLocalMap_surjective block P hr hD (F.frame (i, 0)))
      (degreeFourLocalTarget_eligible block P hr)
      (binaryAffineLocalLinearRepresentation block P).ρ hframe B

end Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
end SymmetricSubgroupAsymptotics

end
