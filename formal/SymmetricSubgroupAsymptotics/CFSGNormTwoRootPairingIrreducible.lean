import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateBase
import Mathlib.LinearAlgebra.RootSystem.Irreducible

/-! Connected actual coordinate pairings force irreducibility. The proof
extracts a coordinate root from an invariant subspace and propagates it
along the literal nonzero matrix entries. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoRootPairing
open CFSGIntegerMatrixPairing
variable {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    (A : Matrix n n ℤ) (hd : ∀ i,A i i=2)
    (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)

theorem coordinate_coroot_eval (i j : n) :
    (rootPairing A hs hp).coroot' (coordinateRoot A hd j)
      ((rootPairing A hs hp).root (coordinateRoot A hd i))=(A i j:ℚ) := by
  rw [RootPairing.root_coroot'_eq_pairing]
  rw [pairing_cast]
  simp only [coordinateRoot,integerPairing,Matrix.toBilin'_single]

private theorem root_mem_of_pairing_ne_zero
    (q : Submodule ℚ (n→ℚ))
    (hq : ∀ a,q∈Module.End.invtSubmodule ((rootPairing A hs hp).reflection a))
    (x : n→ℚ) (hx : x∈q) (a : Roots A)
    (ha : (rootPairing A hs hp).coroot' a x ≠ 0) :
    (rootPairing A hs hp).root a∈q := by
  have hr : (rootPairing A hs hp).reflection a x∈q :=
    (Module.End.mem_invtSubmodule _).mp (hq a) hx
  have hm : ((rootPairing A hs hp).coroot' a x) •
      (rootPairing A hs hp).root a∈q := by
    simpa only [RootPairing.reflection_apply,sub_sub_cancel] using q.sub_mem hx hr
  exact (q.smul_mem_iff ha).mp hm

include hd in
theorem rootPairing_isIrreducible_of_connected
    (hc : ∀ i j,Relation.ReflTransGen (fun a b:n=>A a b≠0) i j) :
    (rootPairing A hs hp).IsIrreducible := by
  apply RootPairing.IsIrreducible.mk'
  intro q hq hne
  obtain ⟨x,hx,hx0⟩ := q.ne_bot_iff.mp hne
  have hseed : ∃ i,rationalPairing A x (Pi.single i 1)≠0 := by
    by_contra! hz
    have he : rationalPairing A x=0 := by
      apply (Pi.basisFun ℚ n).ext
      intro i
      simpa only [Pi.basisFun_apply,LinearMap.zero_apply] using hz i
    apply hx0
    apply rationalPairing_injective A hp
    simpa only [map_zero] using he
  obtain ⟨i,hi⟩ := hseed
  have hstart : (rootPairing A hs hp).root (coordinateRoot A hd i)∈q := by
    apply root_mem_of_pairing_ne_zero A hs hp q hq x hx
    change rationalPairing A x ((rootPairing A hs hp).root (coordinateRoot A hd i))≠0
    rwa [coordinateRoot_root]
  have hall : ∀ j,(rootPairing A hs hp).root (coordinateRoot A hd j)∈q := by
    intro j
    have hpath := hc i j
    induction hpath with
    | refl => exact hstart
    | @tail a b hab hstep ih =>
        apply root_mem_of_pairing_ne_zero A hs hp q hq _ ih
        rw [coordinate_coroot_eval]
        exact_mod_cast hstep
  apply top_unique
  intro y _
  rw [←(Pi.basisFun ℚ n).sum_repr y]
  apply q.sum_mem
  intro j _
  apply q.smul_mem
  simpa only [Pi.basisFun_apply,coordinateRoot_root] using hall j

end SymmetricSubgroupAsymptotics.CFSGNormTwoRootPairing
