import SymmetricSubgroupAsymptotics.ZmudFixedSpaceConstituents
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.LinearAlgebra.TensorProduct.Finiteness
import Mathlib.RepresentationTheory.Intertwining

/-! If one tensor factor is trivial on a subgroup, fixed-free action on
the other factor remains fixed-free. The proof uses the actual tensor
coordinates, not only a kernel or character calculation. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical TensorProduct

namespace SymmetricSubgroupAsymptotics.ZmudTensorFixedSpaces

variable {k G V W : Type} [Field k] [Group G]
  [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]

/-- Fixed-free action on the first factor, with literal trivial action on
all of the second factor. -/
theorem fixedFree_left
    (rho : Representation k G V) (sigma : Representation k G W)
    (N : Subgroup G)
    (hfix : ∀ v : V, (∀ n : N, rho n.1 v = v) → v = 0)
    (htriv : ∀ (n : N) (w : W), sigma n.1 w = w)
    (z : V ⊗[k] W) (hz : ∀ n : N, (rho.tprod sigma) n.1 z = z) : z = 0 := by
  let b := Module.Free.chooseBasis k W
  let e := TensorProduct.equivFinsuppOfBasisRight (M := V) b
  have he (n : N) (z : V ⊗[k] W) (j : Module.Free.ChooseBasisIndex k W) :
      e ((rho.tprod sigma) n.1 z) j = rho n.1 (e z j) := by
    induction z using TensorProduct.induction_on with
    | zero => simp only [map_zero, Finsupp.zero_apply]
    | tmul v w =>
        change (TensorProduct.equivFinsuppOfBasisRight b)
          ((rho.tprod sigma) n.1 (v ⊗ₜ[k] w)) j = _
        rw [Representation.tprod_apply, TensorProduct.map_tmul, htriv n w]
        simp only [e, TensorProduct.equivFinsuppOfBasisRight_apply_tmul_apply,
          map_smul]
    | add z u hz hu =>
        simp only [map_add, Finsupp.add_apply, hz, hu]
  apply e.injective
  rw [map_zero]
  ext j
  apply hfix
  intro n
  have h := he n z j
  rw [hz n] at h
  exact h.symm

/-- The symmetric tensor-factor statement. -/
theorem fixedFree_right
    (rho : Representation k G V) (sigma : Representation k G W)
    (N : Subgroup G)
    (htriv : ∀ (n : N) (v : V), rho n.1 v = v)
    (hfix : ∀ w : W, (∀ n : N, sigma n.1 w = w) → w = 0)
    (z : V ⊗[k] W) (hz : ∀ n : N, (rho.tprod sigma) n.1 z = z) : z = 0 := by
  let e := Representation.TensorProduct.comm rho sigma
  have he : e z = 0 := fixedFree_left sigma rho N hfix htriv (e z) (by
    intro n
    have h := Representation.IntertwiningMap.isIntertwining
      (rho.tprod sigma) (sigma.tprod rho) e.toIntertwiningMap n.1 z
    rw [hz n] at h
    exact h.symm)
  apply e.injective
  simpa only [map_zero] using he

/-- Literal trivial action survives the tensor product. -/
theorem trivial
    (rho : Representation k G V) (sigma : Representation k G W)
    (g : G) (hr : ∀ v, rho g v = v) (hs : ∀ w, sigma g w = w)
    (z : V ⊗[k] W) : (rho.tprod sigma) g z = z := by
  induction z using TensorProduct.induction_on with
  | zero => exact map_zero _
  | tmul v w => rw [Representation.tprod_apply, TensorProduct.map_tmul, hr, hs]
  | add z u hz hu => rw [map_add, hz, hu]

/-- The tensor product of the finite nonzero envelopes used for actual
irreducible constituent selection. -/
def tensor {G : Type} [Group G]
    (E F : ZmudFixedSpaceConstituents.Envelope G) :
    ZmudFixedSpaceConstituents.Envelope G := by
  let b := Module.Free.chooseBasis ℂ F.Space
  letI : Nontrivial (E.Space ⊗[ℂ] F.Space) :=
    (TensorProduct.equivFinsuppOfBasisRight (M := E.Space) b).toEquiv.nontrivial
  exact {
  Space := E.Space ⊗[ℂ] F.Space
  addCommGroup := inferInstance
  module := inferInstance
  finiteDimensional := inferInstance
  nontrivial := inferInstance
  action := E.action.tprod F.action }

end SymmetricSubgroupAsymptotics.ZmudTensorFixedSpaces
