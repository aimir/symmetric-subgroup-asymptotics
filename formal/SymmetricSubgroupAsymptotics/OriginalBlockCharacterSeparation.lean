import SymmetricSubgroupAsymptotics.ImprimitiveBlockEvaluation

/-!
# One local label separates through all ambient conjugates

The literal base-block evaluation already has jointly separating ambient
conjugates.  Hence any local label whose kernel is no larger than the kernel
of that evaluation also separates the original normal block-kernel section
after taking all ambient conjugates.  This is the reusable bridge from a
single affine fibre character to the separating field of a derived-target
certificate.
-/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics

variable {A Omega X C : Type} [Group A] [MulAction A Omega]
  [MulAction A X] [Group C]
  [FaithfulSMul A Omega] [MulAction.IsPretransitive A X]
  (b : Omega → X)
  (hb : ∀ (a : A) (omega : Omega), b (a • omega) = a • b omega)
  (x0 : X)

/-- A label on one literal block coordinate separates a normal section once
its ambient conjugates are retained. -/
theorem originalBlockKernelLabel_conjugates_separate
    (N : Subgroup A) [N.Normal]
    (hN : N ≤ (MulAction.toPermHom A X).ker)
    (label : N →* C)
    (hker : label.ker ≤ (originalBlockEvaluation b hb x0 N hN).ker)
    (n : N)
    (hn : ∀ a : A, label (MulAut.conjNormal a n) = 1) :
    n = 1 := by
  apply originalBlockEvaluation_conjugates_separate b hb x0 N hN n
  intro a
  apply MonoidHom.mem_ker.mp
  exact hker (MonoidHom.mem_ker.mpr (hn a))

end SymmetricSubgroupAsymptotics

end
