import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Projective
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.ZMod.Units
import Mathlib.Tactic.NormNum

/-! The standard GL2(F5) scalar-projective map.
The sole raw premise is the ordinary exceptional group isomorphism,
Allan Adler, *Characterization of modular correspondences by geometric
properties*, Pacific J.Math.155(1992), Lemma13, printed p.17:
https://msp.org/pjm/1992/155-1/pjm-v155-n1-p01-s.pdf.
There is no composition, nonsolubility, or capacity premise. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
attribute [local instance] Fintype.ofFinite
namespace SymmetricSubgroupAsymptotics.StandardGLTwoFiveProjective

abbrev LinearFive := Matrix.GeneralLinearGroup (Fin 2) (ZMod 5)
abbrev ProjectiveFive := Matrix.ProjGenLinGroup (Fin 2) (ZMod 5)

/-- Only the standard exceptional projective isomorphism is imported. -/
def PublishedProjectiveIsomorphism : Prop :=
  Nonempty (ProjectiveFive ≃* Equiv.Perm (Fin 5))

def projectiveEquiv (h : PublishedProjectiveIsomorphism) :
    ProjectiveFive ≃* Equiv.Perm (Fin 5) := Classical.choice h

def projective (h : PublishedProjectiveIsomorphism) : LinearFive →* Equiv.Perm (Fin 5) :=
  (projectiveEquiv h).toMonoidHom.comp Matrix.ProjGenLinGroup.mk

theorem projective_surjective (h : PublishedProjectiveIsomorphism) :
    Function.Surjective (projective h) :=
  (projectiveEquiv h).surjective.comp Matrix.ProjGenLinGroup.mk_surjective

theorem projective_kernel (h : PublishedProjectiveIsomorphism) :
    (projective h).ker = Subgroup.center LinearFive := by
  ext g
  constructor
  · intro hg
    change projectiveEquiv h (Matrix.ProjGenLinGroup.mk g) = 1 at hg
    apply Matrix.ProjGenLinGroup.mk_eq_one.mp
    apply (projectiveEquiv h).injective
    simpa only [map_one] using hg
  · intro hg
    have hm := Matrix.ProjGenLinGroup.mk_eq_one.mpr hg
    change projectiveEquiv h (Matrix.ProjGenLinGroup.mk g) = 1
    rw [hm, map_one]

theorem projective_kernel_central (h : PublishedProjectiveIsomorphism) :
    (projective h).ker ≤ Subgroup.center LinearFive :=
  le_of_eq (projective_kernel h)

abbrev scalarFive : (ZMod 5)ˣ →* LinearFive := Matrix.GeneralLinearGroup.scalar (Fin 2)

def scalarCenter : (ZMod 5)ˣ →* Subgroup.center LinearFive :=
  scalarFive.codRestrict (Subgroup.center LinearFive) (fun u => by
    rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
    exact ⟨u, rfl⟩)

theorem scalarCenter_injective : Function.Injective scalarCenter := by
  intro u v h
  apply Units.ext
  have hd := congrArg (fun z : Subgroup.center LinearFive =>
    z.val.val (0 : Fin 2) (0 : Fin 2)) h
  change Matrix.scalar (Fin 2) (u : ZMod 5) 0 0 =
    Matrix.scalar (Fin 2) (v : ZMod 5) 0 0 at hd
  simpa using hd

theorem scalarCenter_surjective : Function.Surjective scalarCenter := by
  intro z
  have hz : (z : LinearFive) ∈ scalarFive.range := by
    simpa only [Matrix.GeneralLinearGroup.center_eq_range_scalar] using z.property
  obtain ⟨u, hu⟩ := hz
  exact ⟨u, Subtype.ext hu⟩

def scalarCenterEquiv : (ZMod 5)ˣ ≃* Subgroup.center LinearFive :=
  MulEquiv.ofBijective scalarCenter ⟨scalarCenter_injective, scalarCenter_surjective⟩

/-- The isomorphism is with the actual kernel of the chosen projective map. -/
def scalarKernelEquiv (h : PublishedProjectiveIsomorphism) :
    (ZMod 5)ˣ ≃* (projective h).ker :=
  scalarCenterEquiv.trans (MulEquiv.subgroupCongr (projective_kernel h).symm)

theorem card_units_five : Nat.card (ZMod 5)ˣ = 4 := by
  rw [Nat.card_eq_fintype_card]
  decide

theorem card_projective_kernel (h : PublishedProjectiveIsomorphism) :
    Nat.card (projective h).ker = 4 := by
  rw [Nat.card_congr (scalarKernelEquiv h).symm.toEquiv]
  exact card_units_five

theorem card_linearFive : Nat.card LinearFive = 480 := by
  letI : Fact (Nat.Prime 5) := ⟨by decide⟩
  have h := Matrix.card_GL_field (𝔽 := ZMod 5) 2
  norm_num [Fin.prod_univ_succ] at h
  simpa only [LinearFive, Nat.card_eq_fintype_card] using h

end SymmetricSubgroupAsymptotics.StandardGLTwoFiveProjective
