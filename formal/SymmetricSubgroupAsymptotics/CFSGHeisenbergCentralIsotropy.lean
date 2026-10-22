import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.Algebra.Module.ZMod
import Mathlib.Algebra.Field.ZMod
import Lean.Elab.Tactic.Omega

/-! An arbitrary proper central intersection forces the half-dimension
bound in a Heisenberg quotient. The proper intersection need not be zero
and need not be linear over a larger field: the additive-subgroup
corollary works over the actual prime field. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGHeisenbergCentralIsotropy
variable {K V Z : Type*} [Field K]
variable [AddCommGroup V] [Module K V] [AddCommGroup Z] [Module K Z]

def scalarPairing (B : V →ₗ[K] V →ₗ[K] Z) (f : Z →ₗ[K] K) : LinearMap.BilinForm K V where
  toFun x := f.comp (B x)
  map_add' x y := by ext z; simp
  map_smul' a x := by ext z; simp

theorem scalarPairing_apply (B : V →ₗ[K] V →ₗ[K] Z) (f : Z →ₗ[K] K) (x y : V) :
    scalarPairing B f x y = f (B x y) := rfl

theorem scalarPairing_nondegenerate (B : V →ₗ[K] V →ₗ[K] Z)
    (hAlt : ∀ x, B x x = 0)
    (hfull : ∀ x, x ≠ 0 → Function.Surjective (B x))
    (f : Z →ₗ[K] K) (hf : f ≠ 0) : (scalarPairing B f).Nondegenerate := by
  have hz : ∃ z, f z ≠ 0 := by
    by_contra hz
    apply hf
    ext z
    change f z = 0
    by_contra hne
    exact hz ⟨z, hne⟩
  have hA : (scalarPairing B f).IsAlt := by
    intro x
    change f (B x x) = 0
    rw [hAlt, map_zero]
  have hsep : ∀ x, (∀ y, scalarPairing B f x y = 0) → x = 0 := by
    intro x hx
    by_contra hne
    obtain ⟨z, hz⟩ := hz
    obtain ⟨y, hy⟩ := hfull x hne z
    apply hz
    rw [← hy]
    exact hx y
  exact ⟨hsep, fun x hx => hsep x (fun y => hA.isRefl y x (hx y))⟩

theorem twice_finrank_le_of_proper_central_intersection [FiniteDimensional K V]
    (B : V →ₗ[K] V →ₗ[K] Z) (hAlt : ∀ x, B x x = 0)
    (hfull : ∀ x, x ≠ 0 → Function.Surjective (B x))
    (C : Submodule K Z) (hC : C ≠ ⊤) (L : Submodule K V)
    (hL : ∀ x ∈ L, ∀ y ∈ L, B x y ∈ C) :
    2 * Module.finrank K L ≤ Module.finrank K V := by
  obtain ⟨f, hf, hCf⟩ := C.exists_le_ker_of_lt_top (lt_top_iff_ne_top.mpr hC)
  let b := scalarPairing B f
  have hb : b.Nondegenerate := scalarPairing_nondegenerate B hAlt hfull f hf
  have horth : L ≤ b.orthogonal L := by
    intro x hx
    change ∀ y ∈ L, b y x = 0
    intro y hy
    exact hCf (hL y hy x hx)
  have hsum := LinearMap.BilinForm.finrank_add_finrank_orthogonal' (B := b) L
  rw [hb.ker_eq_bot, inf_bot_eq, _root_.finrank_bot, add_zero] at hsum
  have hmono := Submodule.finrank_mono horth
  omega

theorem additive_twice_finrank_le (p : ℕ) [Fact p.Prime]
    [Module (ZMod p) V] [Module (ZMod p) Z] [FiniteDimensional (ZMod p) V]
    (B : V →ₗ[ZMod p] V →ₗ[ZMod p] Z) (hAlt : ∀ x, B x x = 0)
    (hfull : ∀ x, x ≠ 0 → Function.Surjective (B x))
    (C : AddSubgroup Z) (hC : C ≠ ⊤) (L : AddSubgroup V)
    (hL : ∀ x ∈ L, ∀ y ∈ L, B x y ∈ C) :
    2 * Module.finrank (ZMod p) (AddSubgroup.toZModSubmodule p L) ≤
      Module.finrank (ZMod p) V := by
  have hC' : AddSubgroup.toZModSubmodule p C ≠ ⊤ := by
    intro he
    apply hC
    apply (AddSubgroup.toZModSubmodule p).injective
    simpa using he
  exact twice_finrank_le_of_proper_central_intersection B hAlt hfull
    (AddSubgroup.toZModSubmodule p C) hC' (AddSubgroup.toZModSubmodule p L) hL

end SymmetricSubgroupAsymptotics.CFSGHeisenbergCentralIsotropy
