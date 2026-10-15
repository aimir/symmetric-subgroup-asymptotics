import SymmetricSubgroupAsymptotics.BinaryPairStabilizerIndex
import SymmetricSubgroupAsymptotics.CoinducedPairHeadBound
import SymmetricSubgroupAsymptotics.CoinducedQuotientPullback

/-!
The nontrivial pair-kernel branch on the original permutation group.
The local map is descended to the actual stabilizer in the faithful pair
top, then extended to the original pair stabilizer. The original induced
frame consequently has two layers controlled by the quotient induced frame.
The quotient frame bound remains an explicit finite certificate obligation.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SymmetricSubgroupAsymptotics.BinaryPairFrame

variable {X I C V : Type} {U : Subgroup (Equiv.Perm X)}
  [Finite X] [Finite I] [Group C] [Finite C]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  (F : BinaryPairFrame U I) [MulAction.IsPretransitive U X]
  (hker : F.top.ker ≠ ⊥) (i : I)
  (f : F.pointStabilizer i →* C) (hf : Function.Surjective f)
  (hC : Nat.card C = 3 ∨ (Nat.card C = 6 ∧ ¬ IsMulCommutative C))
  (tau : Representation (ZMod 2) C V)

/-- The actual local representation on the faithful quotient stabilizer. -/
abbrev quotientLocalRepresentation :
    Representation (ZMod 2) (F.pairTopStabilizer i) V :=
  tau.comp (F.descendedPointLocalMap hker i f hf hC)

/-- Extension through the original pair stabilizer, killing its pair kernel. -/
abbrev extendedPairRepresentation :
    Representation (ZMod 2) (F.pairStabilizer i) V :=
  (F.quotientLocalRepresentation hker i f hf hC tau).comp
    (F.pairStabilizerTopMap i)

theorem extendedPairRepresentation_restrict :
    (F.extendedPairRepresentation hker i f hf hC tau).comp
      (Subgroup.inclusion (F.pointStabilizer_le_pairStabilizer i)) =
        tau.comp f := by
  apply MonoidHom.ext
  intro h
  change tau (F.descendedPointLocalMap hker i f hf hC
      (F.pointStabilizerTopMap i h)) = tau (f h)
  exact congrArg tau (DFunLike.congr_fun
    (F.descendedPointLocalMap_comp hker i f hf hC) h)

/-- The head bound on the original frame is twice the bound checked on
the literal eight-pair quotient frame. All original local twists survive. -/
theorem originalFrame_head_le_twice
    (cap : ℕ)
    (hquotient : ∀ A : Subrepresentation
      (Representation.coind (F.pairTopStabilizer i).subtype
        (F.quotientLocalRepresentation hker i f hf hC tau)),
      Module.finrank (ZMod 2)
        (A.toRepresentation.IntertwiningMap
          (Representation.trivial (ZMod 2) F.top.range (ZMod 2))) ≤ cap) :
    ∀ B : Subrepresentation
      (Representation.coind (F.pointStabilizer i).subtype (tau.comp f)),
      Module.finrank (ZMod 2)
        (B.toRepresentation.IntertwiningMap
          (Representation.trivial (ZMod 2) U (ZMod 2))) ≤ 2 * cap := by
  let sigma := F.extendedPairRepresentation hker i f hf hC tau
  have hpair : ∀ A : Subrepresentation
      (CoinducedPairFiltration.pairFrame (F.pairStabilizer i) sigma),
      Module.finrank (ZMod 2)
        (A.toRepresentation.IntertwiningMap
          (Representation.trivial (ZMod 2) U (ZMod 2))) ≤ cap := by
    exact CoinducedQuotientPullback.uniform_head_le F.top.rangeRestrict
      (F.pairTopStabilizer i) (F.quotientLocalRepresentation hker i f hf hC tau)
      F.top.rangeRestrict_surjective cap hquotient
  have hpoint := CoinducedPairFiltration.uniform_head_le_twice
    (F.pointStabilizer i) (F.pairStabilizer i)
    (F.pointStabilizer_le_pairStabilizer i) sigma
    (F.stabilizerTwoCosetData hker i) cap hpair
  have hlocal : CoinducedPairFiltration.pointFibre
      (F.pointStabilizer i) (F.pairStabilizer i)
      (F.pointStabilizer_le_pairStabilizer i) sigma = tau.comp f :=
    F.extendedPairRepresentation_restrict hker i f hf hC tau
  change (∀ B : Subrepresentation
    (Representation.coind (F.pointStabilizer i).subtype
      (CoinducedPairFiltration.pointFibre (F.pointStabilizer i) (F.pairStabilizer i)
        (F.pointStabilizer_le_pairStabilizer i) sigma)),
    Module.finrank (ZMod 2)
      (B.toRepresentation.IntertwiningMap
        (Representation.trivial (ZMod 2) U (ZMod 2))) ≤ 2 * cap) at hpoint
  rw [hlocal] at hpoint
  exact hpoint

/-- Numerical form used in the sixteen-point pair branch. -/
theorem originalFrame_head_le_four
    (hquotient : ∀ A : Subrepresentation
      (Representation.coind (F.pairTopStabilizer i).subtype
        (F.quotientLocalRepresentation hker i f hf hC tau)),
      Module.finrank (ZMod 2)
        (A.toRepresentation.IntertwiningMap
          (Representation.trivial (ZMod 2) F.top.range (ZMod 2))) ≤ 2)
    (B : Subrepresentation
      (Representation.coind (F.pointStabilizer i).subtype (tau.comp f))) :
    Module.finrank (ZMod 2)
      (B.toRepresentation.IntertwiningMap
        (Representation.trivial (ZMod 2) U (ZMod 2))) ≤ 4 :=
  F.originalFrame_head_le_twice hker i f hf hC tau 2 hquotient B

end SymmetricSubgroupAsymptotics.BinaryPairFrame

end
