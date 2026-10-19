import SymmetricSubgroupAsymptotics.BinaryTwistedQuartetConstantSocle
import SymmetricSubgroupAsymptotics.BinaryPlaneFunctions

/-! Every actual invariant radical subspace which is not contained in
the constant layer contains that ENTIRE cubic socle. This is the key
submodule statement behind the one-cubic relative-head bound. -/
set_option autoImplicit false
namespace SymmetricSubgroupAsymptotics.BinaryTwistedQuartetRadicalSubmodules
open BinaryTwistedQuartetPolynomial (Bit Plane)
open BinaryTwistedQuartetLoewyCoordinates
open BinaryTwistedQuartetLoewyAugmentations

private theorem add_self_space (v : Space) : v+v=0 := by
  funext i
  exact binaryVector_add_self (v i)

theorem all_constants_of_nonconstant_radical (W : Submodule Bit Space)
    (hcycle : ∀ v, v∈W → cycleAction v∈W)
    (hflip : ∀ v, v∈W → flipAction v∈W)
    (hsecond : ∀ v, v∈W → secondFlip v∈W)
    (v : Space) (hv : v∈W) (hrad : sumBlocks v=0)
    (hnon : v≠constant (v 0)) : ∀ u : Plane, constant u∈W := by
  have hu : v 0+v 3≠0 ∨ v 0+v 2≠0 := by
    by_contra h
    push_neg at h
    have hf : flipAction v=v := by
      apply add_left_cancel (a := v)
      rw [flip_radical v hrad,h.1]
      exact (add_self_space v).symm
    have hs : secondFlip v=v := by
      apply add_left_cancel (a := v)
      rw [second_radical v hrad,h.2]
      exact (add_self_space v).symm
    exact hnon (common_fixed_constant v hf hs)
  rcases hu with hu | hu
  · apply BinaryTwistedQuartetConstantSocle.all_constants_mem W hcycle (v 0+v 3) hu
    rw [← flip_radical v hrad]
    exact W.add_mem hv (hflip v hv)
  · apply BinaryTwistedQuartetConstantSocle.all_constants_mem W hcycle (v 0+v 2) hu
    rw [← second_radical v hrad]
    exact W.add_mem hv (hsecond v hv)

/-- No independent cubic head can survive both above and below the
constant layer: every nonconstant radical submodule absorbs the layer. -/
theorem radical_submodule_dichotomy (W : Submodule Bit Space)
    (hcycle : ∀ v, v∈W → cycleAction v∈W)
    (hflip : ∀ v, v∈W → flipAction v∈W)
    (hsecond : ∀ v, v∈W → secondFlip v∈W)
    (hrad : ∀ v, v∈W → sumBlocks v=0) :
    (∀ v, v∈W → v=constant (v 0)) ∨
      (∀ u : Plane, constant u∈W) := by
  by_cases h : ∀ v, v∈W → v=constant (v 0)
  · exact Or.inl h
  · push_neg at h
    obtain ⟨v,hv,hnon⟩ := h
    exact Or.inr (all_constants_of_nonconstant_radical W hcycle hflip hsecond
      v hv (hrad v hv) hnon)

end SymmetricSubgroupAsymptotics.BinaryTwistedQuartetRadicalSubmodules
