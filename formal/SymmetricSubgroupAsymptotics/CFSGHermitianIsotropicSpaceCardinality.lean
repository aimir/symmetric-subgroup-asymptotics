import SymmetricSubgroupAsymptotics.CFSGHermitianIsotropicSpaceAction
import Mathlib.LinearAlgebra.Projectivization.Cardinality
import Mathlib.Algebra.Module.Submodule.Equiv

/-! Exact finite-field point counts prove that reversible isotropic
incidence transport preserves dimension, including the zero subspace. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped LinearAlgebra.Projectivization
namespace SymmetricSubgroupAsymptotics.CFSGHermitianOrthogonalSpan
variable {K I : Type*} [Field K] [Fintype I]
variable (sigma : K ≃+* K) (H : Matrix I I K)

abbrev PointsInside (S : IsotropicSpace sigma H) := {P : SingularPoint sigma H // P.val ≤ S.val}

def pointsInsideEquiv (S : IsotropicSpace sigma H) :
    PointsInside sigma H S ≃ {L : Submodule K S.val // Module.finrank K L = 1} where
  toFun P := ⟨P.val.val.comap S.val.subtype, by
    have hm : (P.val.val.comap S.val.subtype).map S.val.subtype = P.val.val := by
      rw [Submodule.map_comap_subtype, inf_eq_right.mpr P.property]
    have he := congrArg (fun T : Submodule K (I → K) => Module.finrank K T) hm
    change Module.finrank K ((P.val.val.comap S.val.subtype).map S.val.subtype) =
      Module.finrank K P.val.val at he
    exact (Submodule.finrank_map_subtype_eq S.val _).symm.trans (he.trans P.val.property.1)⟩
  invFun L := ⟨⟨L.val.map S.val.subtype,
    (Submodule.finrank_map_subtype_eq S.val L.val).trans L.property, by
      rintro x ⟨v, _, rfl⟩
      exact S.property v.val v.property v.val v.property⟩, by
    rintro x ⟨v, _, rfl⟩
    exact v.property⟩
  left_inv P := by
    apply Subtype.ext
    apply Subtype.ext
    exact (Submodule.map_comap_subtype S.val P.val.val).trans (inf_eq_right.mpr P.property)
  right_inv L := Subtype.ext (Submodule.comap_map_eq_of_injective S.val.subtype_injective L.val)

theorem pointsInside_card_mul [Finite K] (S : IsotropicSpace sigma H) :
    Nat.card K ^ Module.finrank K S.val =
      Nat.card (PointsInside sigma H S) * (Nat.card K - 1) + 1 := by
  let e : S.val ≃ₗ[K] (Fin (Module.finrank K S.val) → K) := LinearEquiv.ofFinrankEq _ _ (by simp)
  letI : Finite S.val := Finite.of_equiv _ e.symm.toEquiv
  have hp : Nat.card (PointsInside sigma H S) = Nat.card (ℙ K S.val) :=
    (Nat.card_congr (pointsInsideEquiv sigma H S)).trans
      (Nat.card_congr (Projectivization.equivSubmodule K S.val).symm)
  rw [hp]
  have hc : Nat.card S.val = Nat.card K ^ Module.finrank K S.val := by
    rw [Nat.card_congr e.toEquiv, Nat.card_fun, Nat.card_fin]
  exact hc.symm.trans (Projectivization.card' K S.val)

variable (hsep : ∀ S : IsotropicSpace sigma H, SeparatedByMaximal sigma H S.val)
variable (f : Equiv.Perm (SingularPoint sigma H)) (hf : PreservesOrthogonality sigma H f)

def isotropicImagePointsEquiv (S : IsotropicSpace sigma H) :
    PointsInside sigma H S ≃ PointsInside sigma H (isotropicSpaceImage sigma H f hf S) where
  toFun P := ⟨f P.val, (isotropicSpaceEquiv_incidence sigma H hsep f hf S P.val).mpr P.property⟩
  invFun P := ⟨f.symm P.val, (isotropicSpaceEquiv_incidence sigma H hsep f hf S (f.symm P.val)).mp (by
    simpa only [f.apply_symm_apply] using P.property)⟩
  left_inv P := Subtype.ext (f.symm_apply_apply P.val)
  right_inv P := Subtype.ext (f.apply_symm_apply P.val)

include hsep in
theorem isotropicSpaceImage_finrank [Finite K] (S : IsotropicSpace sigma H) :
    Module.finrank K (isotropicSpaceImage sigma H f hf S).val = Module.finrank K S.val := by
  have hc := Nat.card_congr (isotropicImagePointsEquiv sigma H hsep f hf S)
  have hp : Nat.card K ^ Module.finrank K (isotropicSpaceImage sigma H f hf S).val =
      Nat.card K ^ Module.finrank K S.val := by
    rw [pointsInside_card_mul, pointsInside_card_mul, hc]
  exact Nat.pow_right_injective (Nat.succ_le_iff.mpr (Finite.one_lt_card : 1 < Nat.card K)) hp

end SymmetricSubgroupAsymptotics.CFSGHermitianOrthogonalSpan
