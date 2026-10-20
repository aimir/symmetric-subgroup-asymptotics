import SymmetricSubgroupAsymptotics.FiniteGeneratorWord
import Mathlib.GroupTheory.GroupAction.MultipleTransitivity

/-! Original words taking one fixed ordered pair to every distinct ordered
pair prove actual2-transitivity and primitivity. A selected degree12emitter
needs at most144ordered-point states; no group or normal closure is enumerated. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics

structure FiniteTwoPointWordCertificate {X ι : Type*}
    (generators : ι → Equiv.Perm X) where
  firstPoint : X
  secondPoint : X
  distinct : firstPoint≠secondPoint
  words : ∀ x y : X, x≠y → FiniteGeneratorWord ι
  first : ∀ x y hxy, (words x y hxy).eval generators firstPoint=x
  second : ∀ x y hxy, (words x y hxy).eval generators secondPoint=y

namespace FiniteTwoPointWordCertificate
variable {X ι : Type*} {generators : ι → Equiv.Perm X}
    (C : FiniteTwoPointWordCertificate generators)

include C in
/-- Both original coordinates are transported by the same actual word. -/
theorem two_pretransitive :
    MulAction.IsMultiplyPretransitive (Subgroup.closure (Set.range generators)) X 2 := by
  apply MulAction.is_two_pretransitive_iff.mpr
  intro x y z t hxy hzt
  let u : Subgroup.closure (Set.range generators) :=
    ⟨(C.words x y hxy).eval generators,(C.words x y hxy).eval_mem_closure generators⟩
  let v : Subgroup.closure (Set.range generators) :=
    ⟨(C.words z t hzt).eval generators,(C.words z t hzt).eval_mem_closure generators⟩
  have hux : (u : Equiv.Perm X) C.firstPoint=x := C.first x y hxy
  have huy : (u : Equiv.Perm X) C.secondPoint=y := C.second x y hxy
  have hx : (u : Equiv.Perm X).symm x=C.firstPoint := by
    rw [← hux]
    exact (u : Equiv.Perm X).symm_apply_apply C.firstPoint
  have hy : (u : Equiv.Perm X).symm y=C.secondPoint := by
    rw [← huy]
    exact (u : Equiv.Perm X).symm_apply_apply C.secondPoint
  refine ⟨v*u⁻¹,?_,?_⟩
  · change (v : Equiv.Perm X) ((u : Equiv.Perm X).symm x)=z
    rw [hx]
    exact C.first z t hzt
  · change (v : Equiv.Perm X) ((u : Equiv.Perm X).symm y)=t
    rw [hy]
    exact C.second z t hzt

include C in
theorem preprimitive :
    MulAction.IsPreprimitive (Subgroup.closure (Set.range generators)) X :=
  MulAction.isPreprimitive_of_is_two_pretransitive C.two_pretransitive

end FiniteTwoPointWordCertificate
end SymmetricSubgroupAsymptotics
end
