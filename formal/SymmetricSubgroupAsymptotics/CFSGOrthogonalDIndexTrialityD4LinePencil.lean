import Mathlib.LinearAlgebra.Projectivization.Cardinality
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.LinearAlgebra.Dimension.RankNullity
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Data.Fintype.Card
import Lean.Elab.Tactic.Omega

/-! The literal pencil of two-planes through a fixed line is the
projective space of the original quotient. In dimension three it has
q+1 members; deleting one specified plane leaves exactly q. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped LinearAlgebra.Projectivization
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD4LinePencil
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

abbrev PlanesThrough (U : Submodule K V) :=
  {S : Submodule K V // Module.finrank K S = 2 ∧ U ≤ S}

theorem quotient_image_finrank_add (U S : Submodule K V) (hUS : U ≤ S) :
    Module.finrank K (S.map U.mkQ) + Module.finrank K U = Module.finrank K S := by
  have hh := LinearMap.finrank_range_add_finrank_ker (U.mkQ.domRestrict S)
  rw [LinearMap.range_domRestrict, LinearMap.ker_domRestrict, Submodule.ker_mkQ] at hh
  have he := (Submodule.comapSubtypeEquivOfLe hUS).finrank_eq
  rw [he] at hh
  exact hh

def quotientPoint (U : Submodule K V) (hU : Module.finrank K U = 1)
    (S : PlanesThrough U) : ℙ K (V ⧸ U) :=
  Projectivization.mk'' (S.val.map U.mkQ) (by
    have hh := quotient_image_finrank_add U S.val S.property.2
    rw [hU, S.property.1] at hh
    omega)

def liftPoint (U : Submodule K V) (hU : Module.finrank K U = 1)
    (p : ℙ K (V ⧸ U)) : PlanesThrough U :=
  ⟨p.submodule.comap U.mkQ, by
    have hh := quotient_image_finrank_add U (p.submodule.comap U.mkQ)
      (Submodule.le_comap_mkQ U p.submodule)
    rw [Submodule.map_comap_eq_of_surjective U.mkQ_surjective,
      p.finrank_submodule, hU] at hh
    omega, Submodule.le_comap_mkQ U p.submodule⟩

def pencilEquiv (U : Submodule K V) (hU : Module.finrank K U = 1) :
    PlanesThrough U ≃ ℙ K (V ⧸ U) where
  toFun := quotientPoint U hU
  invFun := liftPoint U hU
  left_inv S := by
    apply Subtype.ext
    change (Projectivization.mk'' (S.val.map U.mkQ) _).submodule.comap U.mkQ = S.val
    rw [Projectivization.submodule_mk'', Submodule.comap_map_mkQ,
      sup_eq_right.mpr S.property.2]
  right_inv p := by
    apply Projectivization.submodule_injective
    change (Projectivization.mk'' ((p.submodule.comap U.mkQ).map U.mkQ) _).submodule = p.submodule
    rw [Projectivization.submodule_mk'', Submodule.map_comap_eq_of_surjective U.mkQ_surjective]

theorem planesThrough_card [Finite K] (U : Submodule K V)
    (hU : Module.finrank K U = 1) (hV : Module.finrank K V = 3) :
    Nat.card (PlanesThrough U) = Nat.card K + 1 := by
  have hquot : Module.finrank K (V ⧸ U) = 2 := by
    have hh := U.finrank_quotient_add_finrank
    rw [hU, hV] at hh
    omega
  exact (Nat.card_congr (pencilEquiv U hU)).trans
    (Projectivization.card_of_finrank_two K (V ⧸ U) hquot)

theorem planesThrough_except_card [Finite K] (U : Submodule K V)
    (hU : Module.finrank K U = 1) (hV : Module.finrank K V = 3)
    (R : PlanesThrough U) : Nat.card {S : PlanesThrough U // S ≠ R} = Nat.card K := by
  classical
  let eV : V ≃ₗ[K] (Fin (Module.finrank K V) → K) :=
    LinearEquiv.ofFinrankEq _ _ (by simp)
  letI : Finite V := Finite.of_injective eV eV.injective
  letI : Finite (V ⧸ U) := Finite.of_surjective U.mkQ U.mkQ_surjective
  letI : Finite (PlanesThrough U) := Finite.of_equiv _ (pencilEquiv U hU).symm
  letI : Fintype (PlanesThrough U) := Fintype.ofFinite _
  have hh := planesThrough_card U hU hV
  rw [Nat.card_eq_fintype_card] at hh ⊢
  rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq, hh]
  omega

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD4LinePencil
