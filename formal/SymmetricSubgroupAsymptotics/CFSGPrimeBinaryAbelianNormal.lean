import SymmetricSubgroupAsymptotics.CFSGCliffordBinaryPrimeDimension
import SymmetricSubgroupAsymptotics.CFSGIrreducibleLinearCentralizer
import Mathlib.LinearAlgebra.GeneralLinearGroup.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.GroupTheory.GroupAction.ConjAct
import Mathlib.GroupTheory.Solvable
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finiteness

/-! A faithful irreducible binary group in prime dimension with a prime
number of nonzero vectors is soluble as soon as it has a nontrivial abelian
normal subgroup. This includes the literal dimension-five case. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical IsMulCommutative

namespace SymmetricSubgroupAsymptotics.CFSGPrimeBinaryAbelianNormal

variable {G V : Type} [Group G] [Finite G] [AddCommGroup V]
  [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V] [Finite V]
  (rho : Representation (ZMod 2) G V)

def linearHom : G →* (V ≃ₗ[ZMod 2] V) :=
  (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) V).toMonoidHom.comp
    rho.asGroupHom

omit [Finite G] [FiniteDimensional (ZMod 2) V] [Finite V] in
theorem linearHom_apply (g : G) (x : V) : linearHom rho g x = rho g x := rfl

omit [Finite G] [FiniteDimensional (ZMod 2) V] [Finite V] in
theorem linearHom_injective (hf : Function.Injective rho) :
    Function.Injective (linearHom rho) := by
  intro g h he
  apply hf
  apply LinearMap.ext
  intro x
  exact congrArg (fun e : V ≃ₗ[ZMod 2] V => e x) he

def commutingSubgroupHom (N D : Subgroup G)
    (hc : ∀ (d : D) (n : N), (d : G) * n = n * d) :
    D →* CFSGIrreducibleLinearCentralizer.linearCentralizer (rho.comp N.subtype) where
  toFun d := ⟨linearHom rho d, by
    intro n x
    change rho d (rho n x) = rho n (rho d x)
    have hm := congrArg (fun a : G => rho a x) (hc d n)
    simpa only [map_mul, Module.End.mul_apply] using hm⟩
  map_one' := Subtype.ext (map_one (linearHom rho))
  map_mul' d e := Subtype.ext (map_mul (linearHom rho) (d : G) (e : G))

theorem commutingSubgroupHom_injective (hf : Function.Injective rho)
    (N D : Subgroup G) (hc : ∀ (d : D) (n : N), (d : G) * n = n * d) :
    Function.Injective (commutingSubgroupHom rho N D hc) := by
  intro d e he
  apply Subtype.ext
  exact linearHom_injective rho hf (congrArg Subtype.val he)

theorem soluble_of_nontrivial_abelian_normal
    (hrho : Representation.IsIrreducible rho) (hf : Function.Injective rho)
    (hd : (Module.finrank (ZMod 2) V).Prime)
    {p : ℕ} [Fact p.Prime] (hcard : Nat.card V - 1 = p)
    (N : Subgroup G) [N.Normal] (hN : N ≠ ⊥) [IsMulCommutative N] :
    IsSolvable G := by
  letI : Representation.IsIrreducible (rho.comp N.subtype) :=
    CFSGCliffordBinaryPrimeDimension.normal_restriction_irreducible rho hrho hf hd N hN
  letI : IsCyclic (CFSGIrreducibleLinearCentralizer.linearCentralizer
      (rho.comp N.subtype)) :=
    CFSGIrreducibleLinearCentralizer.centralizer_isCyclic_of_prime_nonzero_card
      (rho.comp N.subtype) hcard
  have hncomm (x y : N) : (x : G) * y = y * x :=
    congrArg Subtype.val (mul_comm x y)
  letI : IsCyclic N := isCyclic_of_injective
    (commutingSubgroupHom rho N N hncomm)
    (commutingSubgroupHom_injective rho hf N N hncomm)
  let theta : G →* MulAut N := MulAut.conjNormal
  have hkcomm (d : theta.ker) (n : N) : (d : G) * n = n * d := by
    have he : theta (d : G) = 1 := MonoidHom.mem_ker.mp d.2
    have hn := congrArg (fun f : MulAut N => (f n : G)) he
    change (d : G) * n * (d : G)⁻¹ = n at hn
    have hh := congrArg (fun z : G => z * (d : G)) hn
    simpa only [mul_assoc, inv_mul_cancel, mul_one] using hh
  letI : IsCyclic theta.ker := isCyclic_of_injective
    (commutingSubgroupHom rho N theta.ker hkcomm)
    (commutingSubgroupHom_injective rho hf N theta.ker hkcomm)
  letI : IsSolvable theta.ker := isSolvable_of_comm (fun x y => mul_comm x y)
  letI : IsSolvable (MulAut N) :=
    solvable_of_solvable_injective
      (f := (IsCyclic.mulAutMulEquiv N).toMonoidHom) (IsCyclic.mulAutMulEquiv N).injective
  exact solvable_of_ker_le_range theta.ker.subtype theta
    (by rw [Subgroup.range_subtype])

theorem soluble_of_nontrivial_abelian_normal_dimension_five
    (hrho : Representation.IsIrreducible rho) (hf : Function.Injective rho)
    (hd : Module.finrank (ZMod 2) V = 5)
    (N : Subgroup G) [N.Normal] (hN : N ≠ ⊥) [IsMulCommutative N] :
    IsSolvable G := by
  letI : Fact (Nat.Prime 31) := ⟨by decide⟩
  have hp : (Module.finrank (ZMod 2) V).Prime := by rw [hd]; decide
  apply soluble_of_nontrivial_abelian_normal rho hrho hf hp
    (p := 31) ?_ N hN
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod, hd]
  decide

end SymmetricSubgroupAsymptotics.CFSGPrimeBinaryAbelianNormal
