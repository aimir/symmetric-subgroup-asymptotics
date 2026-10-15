import SymmetricSubgroupAsymptotics.CoinducedOddPointOrbitCover
import SymmetricSubgroupAsymptotics.QuotientSocleRelativeHead
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoSixteenNaturalFiniteRows
import Mathlib.GroupTheory.GroupAction.MultipleTransitivity

/-! The natural alternating and symmetric sixteen-point actions also
satisfy the original frame budget, without a local quotient exclusion.
An even fifteen-cycle has two original point orbits. Its odd order bounds
the local coinduced head by four; the existing original quotient-socle
certificates give relative rank at most two. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenNaturalOddFrames
open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
open DegreeTwoSixteenNaturalFiniteRows

abbrev top := naturalTopSubgroup

instance top_pretransitive (kind : DegreeTwoSixteenNaturalTop) :
    MulAction.IsPretransitive (top kind) (Fin 16) := by
  cases kind with
  | alternating => exact alternatingGroup.isPretransitive_of_three_le_card (Fin 16) (by simp)
  | symmetric =>
    constructor
    intro x y
    exact ⟨⟨Equiv.swap x y, Subgroup.mem_top _⟩, Equiv.swap_apply_left x y⟩

def cycle : Equiv.Perm (Fin 16) := Fin.cycleRange 14

theorem cycle_mem (kind : DegreeTwoSixteenNaturalTop) : cycle ∈ top kind := by
  cases kind with
  | alternating =>
    change Equiv.Perm.sign cycle = 1
    decide +kernel
  | symmetric => exact Subgroup.mem_top _

def element (kind : DegreeTwoSixteenNaturalTop) : top kind := ⟨cycle, cycle_mem kind⟩

theorem element_pow (kind : DegreeTwoSixteenNaturalTop) : element kind ^ 15 = 1 := by
  apply Subtype.ext
  apply Equiv.ext
  intro x
  change (cycle ^ 15) x = x
  revert x
  decide +kernel

def representatives : Fin 2 → Fin 16 := ![0, 15]

theorem point_cover (kind : DegreeTwoSixteenNaturalTop) : ∀ x : Fin 16,
    ∃ i : Fin 2, ∃ m : Fin 15, element kind ^ m.val • representatives i = x := by
  change ∀ x : Fin 16, ∃ i : Fin 2, ∃ m : Fin 15, (cycle ^ m.val) (representatives i) = x
  decide +kernel

theorem quotientSocle (kind : DegreeTwoSixteenNaturalTop)
    (N : {N : Subgroup (top kind) // N.Normal}) :
    SocleNormalGeneratorBound (top kind ⧸ N.1) 2 := by
  cases kind with
  | alternating => exact alternatingTopSocle N
  | symmetric => exact symmetricTopSocle N

theorem relative_head_le_two (kind : DegreeTwoSixteenNaturalTop)
    (N : Subgroup (top kind)) [N.Normal] :
    Module.finrank (ZMod 2) (primeRelativeCharacters 2 N) ≤ 2 :=
  primeRelativeHead_le_of_all_quotient_socles 2 2 (quotientSocle kind) N

theorem original_head_le_four (kind : DegreeTwoSixteenNaturalTop)
    {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (x : Fin 16) (rho : Representation (ZMod 2) (MulAction.stabilizer (top kind) x) V)
    (hdim : Module.finrank (ZMod 2) V = 2)
    (B : Subrepresentation
      (Representation.coind (MulAction.stabilizer (top kind) x).subtype rho)) :
    Module.finrank (ZMod 2)
      (B.toRepresentation.IntertwiningMap
        (Representation.trivial (ZMod 2) (top kind) (ZMod 2))) ≤ 4 := by
  have hc : ∀ z : Fin 16, ∃ i : Fin 2, ∃ m : ℕ,
      element kind ^ m • representatives i = z := by
    intro z
    obtain ⟨i, m, hm⟩ := point_cover kind z
    exact ⟨i, m.val, hm⟩
  simpa only [hdim, Nat.reduceMul] using
    CoinducedOddPointOrbitCover.binary_head_le_of_odd_cyclic_cover
      x (element kind) 15 (by decide) (element_pow kind) representatives hc rho B

theorem original_frame_sum_le_six (kind : DegreeTwoSixteenNaturalTop)
    {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (x : Fin 16) (rho : Representation (ZMod 2) (MulAction.stabilizer (top kind) x) V)
    (hdim : Module.finrank (ZMod 2) V = 2)
    (N : Subgroup (top kind)) [N.Normal]
    (B : Subrepresentation
      (Representation.coind (MulAction.stabilizer (top kind) x).subtype rho)) :
    Module.finrank (ZMod 2) (primeRelativeCharacters 2 N) +
      Module.finrank (ZMod 2)
        (B.toRepresentation.IntertwiningMap
          (Representation.trivial (ZMod 2) (top kind) (ZMod 2))) ≤ 6 := by
  have hn := relative_head_le_two kind N
  have hb := original_head_le_four kind x rho hdim B
  omega

end SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenNaturalOddFrames
end
