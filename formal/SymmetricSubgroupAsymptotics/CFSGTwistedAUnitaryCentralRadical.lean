import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCentralParameters
import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryRadicalKernel
import Mathlib.GroupTheory.QuotientGroup.Basic

/-! The ACTUAL central parameter line is exactly the kernel of the
actual radical vector-parameter homomorphism. Its injection, centrality
and kernel cardinal are proved on the same literal arrays, all q. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
open CFSGTwistedANaturalMatrices CFSGTwistedAUnitaryUpperArrays
open CFSGTwistedAUnitaryNaturalRadical CFSGSerreOrdinaryTwists

def centralRadicalElement (q : CFSG.PrimePower) (s : ℕ) (c : centralParameters q s) :
    fixedRadical q s :=
  fixedRadicalElement q s 0 c.val (centralParameters_condition q s c.val c.property)

theorem centralRadicalElement_block (q : CFSG.PrimePower) (s : ℕ)
    (c : centralParameters q s) :
    blockFixedMatrixHom q s (centralRadicalElement q s c).val = upperUnit 0 0 c.val := by
  change blockFixedMatrixHom q s
    ⟨(radicalElement q s 0 c.val (centralParameters_condition q s c.val c.property)).val,
      (radicalElement q s 0 c.val (centralParameters_condition q s c.val c.property)).property.2⟩ = _
  rw [blockFixedMatrixHom_radicalElement, firstRow_zero_eq]

def centralRadicalHom (q : CFSG.PrimePower) (s : ℕ) :
    Multiplicative (centralParameters q s) →* fixedRadical q s where
  toFun c := centralRadicalElement q s c.toAdd
  map_one' := by
    change centralRadicalElement q s (0 : centralParameters q s) = 1
    apply Subtype.ext
    apply blockFixedMatrixHom_injective q s
    change blockFixedMatrixHom q s (centralRadicalElement q s 0).val =
      blockFixedMatrixHom q s (1 : CFSGTwistedAUpperUnipotent.naturalFixed (s + 2) q)
    rw [centralRadicalElement_block, map_one]
    apply Units.ext
    exact upperArray_zero
  map_mul' c d := by
    change centralRadicalElement q s (c.toAdd + d.toAdd) =
      centralRadicalElement q s c.toAdd * centralRadicalElement q s d.toAdd
    apply Subtype.ext
    apply blockFixedMatrixHom_injective q s
    change blockFixedMatrixHom q s (centralRadicalElement q s (c.toAdd + d.toAdd)).val =
      blockFixedMatrixHom q s
        ((centralRadicalElement q s c.toAdd).val * (centralRadicalElement q s d.toAdd).val)
    rw [map_mul, centralRadicalElement_block, centralRadicalElement_block,
      centralRadicalElement_block, upperUnit_mul]
    simp only [add_zero, zero_add, dotProduct_zero]
    rfl

theorem centralRadicalHom_injective (q : CFSG.PrimePower) (s : ℕ) :
    Function.Injective (centralRadicalHom q s) := by
  intro c d he
  have hh := congrArg (fun g : fixedRadical q s =>
    (blockFixedMatrixHom q s g.val :
      Matrix (Index (Fin (s + 1))) (Index (Fin (s + 1))) (q.Extension 2))
        (.inl ()) (.inr (.inr ()))) he
  change (blockFixedMatrixHom q s (centralRadicalElement q s c.toAdd).val :
      Matrix (Index (Fin (s + 1))) (Index (Fin (s + 1))) (q.Extension 2))
        (.inl ()) (.inr (.inr ())) =
    (blockFixedMatrixHom q s (centralRadicalElement q s d.toAdd).val :
      Matrix (Index (Fin (s + 1))) (Index (Fin (s + 1))) (q.Extension 2))
        (.inl ()) (.inr (.inr ())) at hh
  rw [centralRadicalElement_block, centralRadicalElement_block] at hh
  apply Multiplicative.toAdd.injective
  apply Subtype.ext
  exact hh

theorem centralRadicalHom_parameter (q : CFSG.PrimePower) (s : ℕ)
    (c : Multiplicative (centralParameters q s)) :
    fixedRadicalParameterHom q s (centralRadicalHom q s c) = 1 := by
  change fixedRadicalParameterHom q s (fixedRadicalElement q s 0 c.toAdd.val
    (centralParameters_condition q s c.toAdd.val c.toAdd.property)) = 1
  rw [fixedRadicalParameterHom_element]
  rfl

theorem exists_centralRadical_of_parameter_one (q : CFSG.PrimePower) (s : ℕ)
    (g : fixedRadical q s) (hg0 : fixedRadicalParameterHom q s g = 1) :
    ∃ c : Multiplicative (centralParameters q s), centralRadicalHom q s c = g := by
  obtain ⟨w, v, b, hg⟩ := g.property
  change Multiplicative.ofAdd (fun i =>
    (blockFixedMatrixHom q s g.val :
      Matrix (Index (Fin (s + 1))) (Index (Fin (s + 1))) (q.Extension 2))
        (.inr (.inl i)) (.inr (.inr ()))) = 1 at hg0
  rw [hg] at hg0
  change Multiplicative.ofAdd v = 1 at hg0
  have hv : v = 0 := congrArg Multiplicative.toAdd hg0
  subst v
  have hs := blockFixedMatrixHom_isometry q s g.val
  rw [hg] at hs
  change ((upperArray w 0 b).map (definingFieldAutomorphism q 2)).transpose *
    blockForm (parity q s) (middleForm q s) * upperArray w 0 b =
      blockForm (parity q s) (middleForm q s) at hs
  have hw : w = 0 := by
    funext i
    have hi := upperArray_isometry_left_entry (definingFieldAutomorphism q 2).toRingHom
      (parity q s) (middleForm q s) w 0 b hs i
    apply (definingFieldAutomorphism q 2).injective
    simpa only [Matrix.mulVec_zero, Pi.zero_apply, add_zero, map_zero] using hi
  subst w
  have hb : b ∈ centralParameters q s := by
    have hi := upperArray_isometry_central_entry (definingFieldAutomorphism q 2).toRingHom
      (parity q s) (middleForm q s) 0 0 b hs
    simpa only [Matrix.mulVec_zero, dotProduct_zero, add_zero] using hi
  refine ⟨Multiplicative.ofAdd ⟨b, hb⟩, ?_⟩
  apply Subtype.ext
  apply blockFixedMatrixHom_injective q s
  change blockFixedMatrixHom q s (centralRadicalElement q s ⟨b, hb⟩).val =
    blockFixedMatrixHom q s g.val
  rw [centralRadicalElement_block]
  exact hg.symm

def centralRadicalKernelHom (q : CFSG.PrimePower) (s : ℕ) :
    Multiplicative (centralParameters q s) →* (fixedRadicalParameterHom q s).ker where
  toFun c := ⟨centralRadicalHom q s c, centralRadicalHom_parameter q s c⟩
  map_one' := Subtype.ext (map_one (centralRadicalHom q s))
  map_mul' c d := Subtype.ext (map_mul (centralRadicalHom q s) c d)

def centralRadicalKernelEquiv (q : CFSG.PrimePower) (s : ℕ) :
    Multiplicative (centralParameters q s) ≃* (fixedRadicalParameterHom q s).ker :=
  MulEquiv.ofBijective (centralRadicalKernelHom q s)
    ⟨fun _ _ he => centralRadicalHom_injective q s (congrArg Subtype.val he), by
      rintro ⟨g, hg⟩
      obtain ⟨c, hc⟩ := exists_centralRadical_of_parameter_one q s g hg
      exact ⟨c, Subtype.ext hc⟩⟩

theorem fixedRadicalParameterHom_kernel_card (q : CFSG.PrimePower) (s : ℕ) :
    Nat.card (fixedRadicalParameterHom q s).ker = q.order := by
  calc
    _ = Nat.card (Multiplicative (centralParameters q s)) :=
      (Nat.card_congr (centralRadicalKernelEquiv q s).toEquiv).symm
    _ = Nat.card (centralParameters q s) := Nat.card_congr Multiplicative.toAdd
    _ = q.order := centralParameters_card q s

theorem centralRadicalHom_mem_center (q : CFSG.PrimePower) (s : ℕ)
    (c : Multiplicative (centralParameters q s)) :
    centralRadicalHom q s c ∈ Subgroup.center (fixedRadical q s) := by
  apply Subgroup.mem_center_iff.mpr
  intro g
  obtain ⟨w, v, b, hg⟩ := g.property
  apply Subtype.ext
  apply blockFixedMatrixHom_injective q s
  change blockFixedMatrixHom q s (g.val * (centralRadicalElement q s c.toAdd).val) =
    blockFixedMatrixHom q s ((centralRadicalElement q s c.toAdd).val * g.val)
  simp only [map_mul]
  rw [centralRadicalElement_block, hg, upperUnit_mul, upperUnit_mul]
  simp only [zero_add, add_zero, dotProduct_zero, zero_dotProduct]
  congr 1
  exact add_comm _ _

end SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
