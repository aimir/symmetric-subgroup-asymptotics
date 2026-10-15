import SymmetricSubgroupAsymptotics.BinaryPairOriginalFrameHead
import SymmetricSubgroupAsymptotics.BinaryPairPrimePowerNormalHead

/-! The numerical sixteen-point pair branch on its original group.
The two inputs are precisely the top and local-frame bounds of the actual
eight-pair quotient. The output retains every original normal subgroup and
every correlated subrepresentation of the original induced frame. -/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics.BinaryPairFrame

variable {X I C V : Type} {U : Subgroup (Equiv.Perm X)}
  [Finite X] [Finite I] [Group C] [Finite C]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  (F : BinaryPairFrame U I) [MulAction.IsPretransitive U X]
  (hker : F.top.ker ≠ ⊥) (hcard : Nat.card I = 8) (i : I)
  (f : F.pointStabilizer i →* C) (hf : Function.Surjective f)
  (hC : Nat.card C = 3 ∨ (Nat.card C = 6 ∧ ¬ IsMulCommutative C))
  (tau : Representation (ZMod 2) C V)

include hcard in
/-- The required ten-slot sum follows from 6 + 4. No sharp scalar-module
bound or splitting assumption is needed for the nontrivial-kernel branch. -/
theorem original_sum_le_ten
    (htop : ∀ (M : Subgroup F.top.range) [M.Normal],
      Module.finrank (ZMod 2) (primeRelativeCharacters 2 M) ≤ 2)
    (hquotient : ∀ A : Subrepresentation
      (Representation.coind (F.pairTopStabilizer i).subtype
        (F.quotientLocalRepresentation hker i f hf hC tau)),
      Module.finrank (ZMod 2)
        (A.toRepresentation.IntertwiningMap
          (Representation.trivial (ZMod 2) F.top.range (ZMod 2))) ≤ 2)
    (N : Subgroup U) [N.Normal]
    (B : Subrepresentation
      (Representation.coind (F.pointStabilizer i).subtype (tau.comp f))) :
    Module.finrank (ZMod 2) (primeRelativeCharacters 2 N) +
      Module.finrank (ZMod 2)
        (B.toRepresentation.IntertwiningMap
          (Representation.trivial (ZMod 2) U (ZMod 2))) ≤ 10 := by
  letI : Nontrivial I := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  letI : MulAction U I := MulAction.compHom I F.top
  letI : MulAction.IsPretransitive U I := by
    constructor
    intro a b
    obtain ⟨u, hu⟩ := MulAction.exists_smul_eq U (F.frame (a, 0)) (F.frame (b, 0))
    refine ⟨u, ?_⟩
    have h := F.intertwine u (a, 0)
    change (F.frame.symm (u • F.frame (a, 0))).1 = F.top u a at h
    rw [hu, Equiv.symm_apply_apply] at h
    exact h.symm
  have hn := F.eightPair_relativeHead_le_six (fun _ _ => rfl) hcard htop N
  have hb := F.originalFrame_head_le_four hker i f hf hC tau hquotient B
  exact Nat.add_le_add hn hb

end SymmetricSubgroupAsymptotics.BinaryPairFrame

end
