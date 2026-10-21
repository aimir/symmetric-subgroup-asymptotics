import SymmetricSubgroupAsymptotics.TwoGroupTernaryInvariantLine
import SymmetricSubgroupAsymptotics.NormalInvariantLineEigenbasis
import Mathlib.RepresentationTheory.Basic

/-! A normal2-group in an irreducible ternary3-space has a common
eigenbasis on the original space. No Maschke or Clifford theorem is
needed: a fixed projective line and its ambient conjugates span the space. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical LinearAlgebra.Projectivization
namespace SymmetricSubgroupAsymptotics.NormalTwoGroupTernaryEigenbasis
local instance : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩

variable {G V : Type} [Group G] [AddCommGroup V] [Module (ZMod 3) V] [Finite V]

theorem exists_eigenbasis
    (rho : Representation (ZMod 3) G V)
    (hrho : Representation.IsIrreducible rho)
    (hdim : Module.finrank (ZMod 3) V=3)
    (N : Subgroup G) [N.Normal] (hN : IsPGroup 2 N) :
    ∃ b : Module.Basis (Fin 3) (ZMod 3) V,
      ∀ (n : N) (i : Fin 3),∃ a : ZMod 3,rho n.val (b i)=a • b i := by
  letI : DistribMulAction N V := DistribMulAction.compHom V
    (Representation.asGroupHom (rho.comp N.subtype))
  letI : SMulCommClass N (ZMod 3) V := ⟨fun n a v => (rho n.val).map_smul a v⟩
  obtain ⟨p,hp⟩ := TwoGroupTernaryInvariantLine.fixed_projective hN hdim
  have hline (n : N) : ∃ a : ZMod 3,rho n.val p.rep=a • p.rep := by
    have he : Projectivization.mk (ZMod 3) (n • p.rep)
        ((smul_ne_zero_iff_ne n).mpr p.rep_nonzero)=p := by
      exact (Projectivization.smul_mk n p.rep_nonzero).symm.trans
        ((congrArg (fun q : Projectivization (ZMod 3) V => n • q) p.mk_rep).trans (hp n))
    have hm : n • p.rep∈p.submodule := by
      have hs := congrArg Projectivization.submodule he
      change Submodule.span (ZMod 3) {n • p.rep}=p.submodule at hs
      rw [←hs]
      exact Submodule.mem_span_singleton_self _
    have hspan : p.submodule=Submodule.span (ZMod 3) {p.rep} := p.submodule_eq
    rw [hspan] at hm
    obtain ⟨a,ha⟩ := Submodule.mem_span_singleton.mp hm
    exact ⟨a,ha.symm⟩
  exact NormalInvariantLineEigenbasis.exists_eigenbasis_three rho hrho hdim N
    p.rep p.rep_nonzero hline

end SymmetricSubgroupAsymptotics.NormalTwoGroupTernaryEigenbasis
