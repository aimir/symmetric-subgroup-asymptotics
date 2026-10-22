import SymmetricSubgroupAsymptotics.CFSGCliffordConstituentDimension
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Group
import Mathlib.Algebra.Group.Subgroup.Lattice

/-! Prime-dimensional faithful irreducible binary modules remain irreducible
on every nontrivial normal subgroup. The obstruction from Clifford theory
would be a one-dimensional binary constituent, which is necessarily trivial. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical MonoidAlgebra DirectSum

namespace SymmetricSubgroupAsymptotics.CFSGCliffordBinaryPrimeDimension

variable {G V : Type} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]

theorem one_dimensional_representation_trivial
    (rho : Representation (ZMod 2) G V)
    (hd : Module.finrank (ZMod 2) V = 1) (g : G) (x : V) : rho g x = x := by
  obtain ⟨c, hc, _⟩ :=
    LinearMap.existsUnique_eq_smul_id_of_finrank_eq_one hd (rho g)
  have hc01 : c = 0 ∨ c = 1 := (show ∀ a : ZMod 2, a = 0 ∨ a = 1 by decide) c
  rcases hc01 with rfl | rfl
  · have hz : rho g = 0 := by simpa only [zero_smul] using hc
    have hx : x = 0 := (Representation.apply_bijective rho g).1 (by
      rw [hz]
      rfl)
    simp only [hx, map_zero]
  · simpa only [one_smul] using congrArg (fun f : V →ₗ[ZMod 2] V => f x) hc

variable [Finite G]

theorem normal_restriction_trivial_of_trivial_constituent
    (rho : Representation (ZMod 2) G V)
    (hrho : Representation.IsIrreducible rho)
    (H : Subgroup G) [H.Normal]
    (W : Subrepresentation (rho.comp H.subtype))
    (hW : Representation.IsIrreducible W.toRepresentation)
    (htriv : ∀ (h : H) (w : W.toSubmodule), W.toRepresentation h w = w)
    (h : H) (x : V) : rho h x = x := by
  obtain ⟨n, g, hinternal, _, _, _⟩ :=
    Theory.Representation.isaacs_theorem_6_5.{0, 0, 0, 0} rho H hrho W hW
  let rhoH : Representation (ZMod 2) H V := rho.comp H.subtype
  let A : Fin n → Submodule (ZMod 2)[H] rhoH.asModule := fun i =>
    (Theory.Representation.conjugateSubrepresentation rho H W (g i)).asSubmodule
  let e := LinearEquiv.ofBijective (DirectSum.coeLinearMap A) hinternal
  have hWfix (a : H) (w : V) (hw : w ∈ W) : rho a w = w :=
    congrArg Subtype.val (htriv a ⟨w, hw⟩)
  have hAfix (i : Fin n) (z : A i) : rho h z.1 = z.1 := by
    have hz := z.2
    change z.1 ∈ Submodule.map (rho (g i)⁻¹) W.toSubmodule at hz
    obtain ⟨w, hw, he⟩ := hz
    rw [← he]
    let a : H := ⟨g i * (h : G) * (g i)⁻¹,
      Subgroup.Normal.conj_mem (inferInstance : H.Normal) h h.2 (g i)⟩
    have hm : (h : G) * (g i)⁻¹ = (g i)⁻¹ * (a : G) := by
      dsimp only [a]
      group
    calc
      rho h (rho (g i)⁻¹ w) = rho ((h : G) * (g i)⁻¹) w := by
        simp only [map_mul, Module.End.mul_apply]
      _ = rho (g i)⁻¹ (rho a w) := by
        rw [hm]
        simp only [map_mul, Module.End.mul_apply]
      _ = rho (g i)⁻¹ w := by rw [hWfix a w hw]
  let y : rhoH.asModule := rhoH.asModuleEquiv.symm x
  have hsum' : y = ∑ i : Fin n, (e.symm y i).1 := by
    calc
      y = DirectSum.coeLinearMap A (e.symm y) := (e.apply_symm_apply y).symm
      _ = ∑ i : Fin n, (e.symm y i).1 := by
        change DFinsupp.sumAddHom (fun i => (A i).subtype.toAddMonoidHom) (e.symm y) = _
        rw [DFinsupp.sumAddHom_apply, DFinsupp.sum_eq_sum_fintype]
        · rfl
        · intro i
          rfl
  have hsum : x = ∑ i : Fin n, rhoH.asModuleEquiv (e.symm y i).1 := by
    have heq := congrArg rhoH.asModuleEquiv hsum'
    simpa only [y, LinearEquiv.apply_symm_apply, map_sum] using heq
  calc
    rho h x = rho h (∑ i : Fin n, rhoH.asModuleEquiv (e.symm y i).1) :=
      congrArg (rho h) hsum
    _ = ∑ i : Fin n, rho h (rhoH.asModuleEquiv (e.symm y i).1) := map_sum _ _ _
    _ = ∑ i : Fin n, rhoH.asModuleEquiv (e.symm y i).1 :=
      Finset.sum_congr rfl (fun i _ => hAfix i (e.symm y i))
    _ = x := hsum.symm

theorem normal_restriction_irreducible
    (rho : Representation (ZMod 2) G V)
    (hrho : Representation.IsIrreducible rho) (hf : Function.Injective rho)
    (hp : (Module.finrank (ZMod 2) V).Prime)
    (H : Subgroup G) [H.Normal] (hH : H ≠ ⊥) :
    Representation.IsIrreducible (rho.comp H.subtype) := by
  rcases CFSGCliffordConstituentDimension.restriction_irreducible_or_one_dimensional
      rho H hrho hp with hi | ⟨W, hW, hd⟩
  · exact hi
  · exfalso
    apply hH
    apply (Subgroup.eq_bot_iff_forall _).mpr
    intro h hh
    apply hf
    apply LinearMap.ext
    intro x
    simpa only [map_one, Module.End.one_apply] using
      normal_restriction_trivial_of_trivial_constituent rho hrho H W hW
        (one_dimensional_representation_trivial W.toRepresentation hd) ⟨h, hh⟩ x

end SymmetricSubgroupAsymptotics.CFSGCliffordBinaryPrimeDimension
