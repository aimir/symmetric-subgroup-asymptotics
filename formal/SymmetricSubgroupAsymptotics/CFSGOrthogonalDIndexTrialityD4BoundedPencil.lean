import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD4LinePencil

/-! A pencil inside a specified original three-space is counted by
restriction to that SAME subspace. Both containment equations survive
the equivalence; no abstract replacement of the ambient space occurs. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD4LinePencil
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

abbrev PlaneInterval (U W : Submodule K V) :=
  {S : Submodule K V // Module.finrank K S = 2 ∧ U ≤ S ∧ S ≤ W}

def intervalRestriction (U W : Submodule K V) (S : PlaneInterval U W) :
    PlanesThrough (U.comap W.subtype) :=
  ⟨S.val.comap W.subtype,
    (Submodule.comapSubtypeEquivOfLe S.property.2.2).finrank_eq.trans S.property.1,
    Submodule.comap_mono S.property.2.1⟩

def intervalExtension (U W : Submodule K V) (hUW : U ≤ W)
    (S : PlanesThrough (U.comap W.subtype)) : PlaneInterval U W :=
  ⟨S.val.map W.subtype, (Submodule.finrank_map_subtype_eq W S.val).trans S.property.1,
    by
      intro u hu
      exact ⟨⟨u, hUW hu⟩, S.property.2 hu, rfl⟩,
    by rintro x ⟨u, hu, rfl⟩; exact u.property⟩

def intervalPencilEquiv (U W : Submodule K V) (hUW : U ≤ W) :
    PlaneInterval U W ≃ PlanesThrough (U.comap W.subtype) where
  toFun := intervalRestriction U W
  invFun := intervalExtension U W hUW
  left_inv S := by
    apply Subtype.ext
    change (S.val.comap W.subtype).map W.subtype = S.val
    rw [Submodule.map_comap_subtype, inf_eq_right.mpr S.property.2.2]
  right_inv S := by
    apply Subtype.ext
    change (S.val.map W.subtype).comap W.subtype = S.val
    exact Submodule.comap_map_eq_of_injective W.subtype_injective S.val

theorem planeInterval_card [Finite K] (U W : Submodule K V) (hUW : U ≤ W)
    (hU : Module.finrank K U = 1) (hW : Module.finrank K W = 3) :
    Nat.card (PlaneInterval U W) = Nat.card K + 1 := by
  have hi : Module.finrank K (U.comap W.subtype) = 1 :=
    (Submodule.comapSubtypeEquivOfLe hUW).finrank_eq.trans hU
  exact (Nat.card_congr (intervalPencilEquiv U W hUW)).trans
    (planesThrough_card (U.comap W.subtype) hi hW)

theorem planeInterval_except_card [Finite K] (U W : Submodule K V) (hUW : U ≤ W)
    (hU : Module.finrank K U = 1) (hW : Module.finrank K W = 3)
    (R : PlaneInterval U W) :
    Nat.card {S : PlaneInterval U W // S ≠ R} = Nat.card K := by
  classical
  have hi : Module.finrank K (U.comap W.subtype) = 1 :=
    (Submodule.comapSubtypeEquivOfLe hUW).finrank_eq.trans hU
  let eW : W ≃ₗ[K] (Fin 3 → K) := LinearEquiv.ofFinrankEq _ _ (by simpa using hW)
  letI : Finite W := Finite.of_injective eW eW.injective
  letI : Finite (W ⧸ U.comap W.subtype) :=
    Finite.of_surjective (U.comap W.subtype).mkQ (U.comap W.subtype).mkQ_surjective
  let e := (intervalPencilEquiv U W hUW).trans (pencilEquiv _ hi)
  letI : Finite (PlaneInterval U W) := Finite.of_equiv _ e.symm
  letI : Fintype (PlaneInterval U W) := Fintype.ofFinite _
  have hh := planeInterval_card U W hUW hU hW
  rw [Nat.card_eq_fintype_card] at hh ⊢
  rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq, hh]
  omega

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD4LinePencil
