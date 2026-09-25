import SymmetricSubgroupAsymptotics.NoncanonicalLifts
import SymmetricSubgroupAsymptotics.RetainedQuadraticAnnihilator
import SymmetricSubgroupAsymptotics.ExceptionalIncidence

/-!
# Exceptional bounds for actual subgroups of a central binary extension

The fixed-image lift identity is assembled over literal subgroups. Original
square annihilators are transported by an actual dual-coordinate isomorphism,
with their complete subspaces and all lift weights retained.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics

attribute [local instance] Fintype.ofFinite

variable {ι W : Type*} [Fintype ι] [AddCommGroup W] [Module (ZMod 2) W]
  {V : ι → Type*} [∀ i, AddCommGroup (V i)] [∀ i, Module (ZMod 2) (V i)]

/-- The actual quotient image projects fully to every quadratic coordinate. -/
def FullBinaryQuotientImage {R : ℕ}
    (e : (Fin R → ZMod 2) ≃ₗ[ZMod 2] (W × ∀ i, V i))
    (U : Submodule (ZMod 2) (Fin R → ZMod 2)) : Prop :=
  ∀ i, Function.Surjective (fun u : U ↦ (e u.val).2 i)

/-- Literal noncanonical subgroups whose actual quotient image is full on
the indicated coordinates. A quotient-image presentation is only a property. -/
def FullNoncanonicalBinarySubgroup {G : Type*} [Group G] {R : ℕ}
    (π : G →* Multiplicative (Fin R → ZMod 2))
    (e : (Fin R → ZMod 2) ≃ₗ[ZMod 2] (W × ∀ i, V i)) :=
  {H : Subgroup G // ¬ π.ker ≤ H ∧
    ∃ U : Submodule (ZMod 2) (Fin R → ZMod 2),
      H.map π = U.toAddSubgroup.toSubgroup ∧ FullBinaryQuotientImage e U}

/-- Exact partition of the physical subgroup family by its unique actual
binary image. -/
def fullNoncanonicalBinarySubgroupEquiv {G : Type*} [Group G] {R : ℕ}
    (π : G →* Multiplicative (Fin R → ZMod 2))
    (e : (Fin R → ZMod 2) ≃ₗ[ZMod 2] (W × ∀ i, V i)) :
    (Σ U : {U : Submodule (ZMod 2) (Fin R → ZMod 2) // FullBinaryQuotientImage e U},
      {H : Subgroup G // H.map π = U.val.toAddSubgroup.toSubgroup ∧ ¬ π.ker ≤ H}) ≃
        FullNoncanonicalBinarySubgroup π e := by
  let f : (Σ U : {U : Submodule (ZMod 2) (Fin R → ZMod 2) // FullBinaryQuotientImage e U},
      {H : Subgroup G // H.map π = U.val.toAddSubgroup.toSubgroup ∧ ¬ π.ker ≤ H}) →
        FullNoncanonicalBinarySubgroup π e :=
    fun p ↦ ⟨p.2.val,p.2.property.2,p.1.val,p.2.property.1,p.1.property⟩
  refine Equiv.ofBijective f ⟨?_,?_⟩
  · rintro ⟨U,H⟩ ⟨U',H'⟩ he
    have hH : H.val = H'.val := congrArg Subtype.val he
    have hU : U=U' := by
      apply Subtype.ext
      apply (binarySubmoduleSubgroupOrderIso R).injective
      exact H.property.1.symm.trans ((congrArg (fun H : Subgroup G ↦ H.map π) hH).trans H'.property.1)
    subst U'
    have hh : H=H' := Subtype.ext hH
    subst H'
    rfl
  · rintro ⟨H,hker,U,hU,hfull⟩
    exact ⟨⟨⟨U,hfull⟩,⟨H,hU,hker⟩⟩,rfl⟩

/-- The original nonzero annihilator subspaces transported to their actual
coordinate subspaces, without replacing either one by its dimension. -/
def originalQuadraticAnnihilatorEquiv {G : Type*} [Group G] {R : ℕ}
    (π : G →* Multiplicative (Fin R → ZMod 2)) (hπ : Function.Surjective π)
    (κ : Multiplicative (ι → ZMod 2) ≃* π.ker)
    (e : (Fin R → ZMod 2) ≃ₗ[ZMod 2] (W × ∀ i, V i))
    (q : ∀ i, QuadraticForm (ZMod 2) (V i))
    (hsq : ∀ g : G, binarySquareCoordinate π κ g = fun i ↦ q i ((e (π g).toAdd).2 i))
    (U : Submodule (ZMod 2) (Fin R → ZMod 2)) :
    {B : Submodule (ZMod 2) (Module.Dual (ZMod 2) (ι → ZMod 2)) //
      B ≤ (binaryImageSquareObstruction π κ U).dualAnnihilator ∧ B ≠ ⊥} ≃
    {B : Submodule (ZMod 2) (ι → ZMod 2) //
      B ≤ quadraticCoordinateAnnihilator e q U ∧ B ≠ ⊥} := by
  let s := Submodule.orderIsoMapComap (binaryDualCoordinates (ι := ι))
  have hA : s (binaryImageSquareObstruction π κ U).dualAnnihilator =
      quadraticCoordinateAnnihilator e q U := by
    rw [binaryImageSquareObstruction_eq_quadraticValueSpan π hπ κ e q hsq U]
    rfl
  apply Equiv.subtypeEquiv s.toEquiv
  intro B
  change (B ≤ (binaryImageSquareObstruction π κ U).dualAnnihilator ∧ B ≠ ⊥) ↔
    (s B ≤ quadraticCoordinateAnnihilator e q U ∧ s B ≠ ⊥)
  rw [← hA]
  exact and_congr s.le_iff_le.symm (not_congr (map_eq_bot_iff s).symm)

theorem originalQuadraticAnnihilatorEquiv_finrank {G : Type*} [Group G] {R : ℕ}
    (π : G →* Multiplicative (Fin R → ZMod 2)) (hπ : Function.Surjective π)
    (κ : Multiplicative (ι → ZMod 2) ≃* π.ker)
    (e : (Fin R → ZMod 2) ≃ₗ[ZMod 2] (W × ∀ i, V i))
    (q : ∀ i, QuadraticForm (ZMod 2) (V i))
    (hsq : ∀ g : G, binarySquareCoordinate π κ g = fun i ↦ q i ((e (π g).toAdd).2 i))
    (U : Submodule (ZMod 2) (Fin R → ZMod 2))
    (B : {B : Submodule (ZMod 2) (Module.Dual (ZMod 2) (ι → ZMod 2)) //
      B ≤ (binaryImageSquareObstruction π κ U).dualAnnihilator ∧ B ≠ ⊥}) :
    Module.finrank (ZMod 2) (originalQuadraticAnnihilatorEquiv π hπ κ e q hsq U B).val =
      Module.finrank (ZMod 2) B.val :=
  ((binaryDualCoordinates (ι := ι)).submoduleMap B.val).finrank_eq.symm

private theorem sum_subtype_eq_indicator {A : Type*} [Fintype A]
    (p : A → Prop) (f : A → ℝ) :
    (∑ a : {a // p a}, f a.val) = ∑ a, if p a then f a else 0 := by
  rw [← Finset.sum_filter]
  exact (Finset.sum_subtype (Finset.univ.filter p) (by simp) f).symm

private theorem sum_nonzero_below_eq_indicator {E : Type*} [AddCommGroup E]
    [Module (ZMod 2) E] [Finite E] (A : Submodule (ZMod 2) E)
    (f : Submodule (ZMod 2) E → ℝ) :
    (∑ B : {B : Submodule (ZMod 2) E // B ≤ A ∧ B ≠ ⊥}, f B.val) =
      ∑ B : {B : Submodule (ZMod 2) E // B ≠ ⊥}, if B.val ≤ A then f B.val else 0 := by
  let e := (Equiv.subtypeSubtypeEquivSubtypeInter
    (fun B : Submodule (ZMod 2) E ↦ B ≠ ⊥) (fun B ↦ B ≤ A)).trans
    (Equiv.subtypeEquivRight fun _ ↦ and_comm)
  calc
    _ = ∑ B : {B : {B : Submodule (ZMod 2) E // B ≠ ⊥} // B.val ≤ A}, f B.val.val :=
      (Fintype.sum_equiv e (fun B ↦ f B.val.val) (fun B ↦ f B.val) (fun _ ↦ rfl)).symm
    _ = _ := sum_subtype_eq_indicator
      (fun B : {B : Submodule (ZMod 2) E // B ≠ ⊥} ↦ B.val ≤ A) (fun B ↦ f B.val)

private instance : Finite (Module.Dual (ZMod 2) (ι → ZMod 2)) :=
  Finite.of_injective (fun f : Module.Dual (ZMod 2) (ι → ZMod 2) ↦
    (f : (ι → ZMod 2) → ZMod 2)) DFunLike.coe_injective

/-- Exact fixed-image physical count in the actual quadratic coordinates. -/
theorem binary_image_noncanonical_lifts_count_quadratic {G : Type*} [Group G] [Finite G] {R : ℕ}
    (π : G →* Multiplicative (Fin R → ZMod 2)) (hπ : Function.Surjective π)
    (κ : Multiplicative (ι → ZMod 2) ≃* π.ker) (hcentral : π.ker ≤ Subgroup.center G)
    (e : (Fin R → ZMod 2) ≃ₗ[ZMod 2] (W × ∀ i, V i))
    (q : ∀ i, QuadraticForm (ZMod 2) (V i))
    (hsq : ∀ g : G, binarySquareCoordinate π κ g = fun i ↦ q i ((e (π g).toAdd).2 i))
    (U : Submodule (ZMod 2) (Fin R → ZMod 2)) :
    (Nat.card {H : Subgroup G // H.map π = U.toAddSubgroup.toSubgroup ∧ ¬ π.ker ≤ H} : ℝ) =
      ∑ B : {B : Submodule (ZMod 2) (ι → ZMod 2) //
        B ≤ quadraticCoordinateAnnihilator e q U ∧ B ≠ ⊥},
        (2 : ℝ) ^ (Module.finrank (ZMod 2) U * Module.finrank (ZMod 2) B.val) := by
  rw [binary_image_noncanonical_lifts_count_original_annihilator_real π hπ κ hcentral U]
  exact Fintype.sum_equiv (originalQuadraticAnnihilatorEquiv π hπ κ e q hsq U) _ _
    (fun B ↦ by rw [originalQuadraticAnnihilatorEquiv_finrank])

/-- The complete physical noncanonical subgroup count equals the actual
weighted incidence sum. No desired count or incidence bound is a premise. -/
theorem fullNoncanonicalBinarySubgroup_card_eq_incidence {G : Type*} [Group G] [Finite G] {R : ℕ}
    (π : G →* Multiplicative (Fin R → ZMod 2)) (hπ : Function.Surjective π)
    (κ : Multiplicative (ι → ZMod 2) ≃* π.ker) (hcentral : π.ker ≤ Subgroup.center G)
    (e : (Fin R → ZMod 2) ≃ₗ[ZMod 2] (W × ∀ i, V i))
    (q : ∀ i, QuadraticForm (ZMod 2) (V i))
    (hsq : ∀ g : G, binarySquareCoordinate π κ g = fun i ↦ q i ((e (π g).toAdd).2 i)) :
    (Nat.card (FullNoncanonicalBinarySubgroup π e) : ℝ) = exceptionalQuadraticIncidence e q := by
  classical
  calc
    _ = ∑ U : {U : Submodule (ZMod 2) (Fin R → ZMod 2) // FullBinaryQuotientImage e U},
        (Nat.card {H : Subgroup G // H.map π = U.val.toAddSubgroup.toSubgroup ∧ ¬ π.ker ≤ H} : ℝ) := by
      rw [← Nat.card_congr (fullNoncanonicalBinarySubgroupEquiv π e),Nat.card_sigma,Nat.cast_sum]
    _ = ∑ U : {U : Submodule (ZMod 2) (Fin R → ZMod 2) // FullBinaryQuotientImage e U},
        ∑ B : {B : Submodule (ZMod 2) (ι → ZMod 2) // B ≠ ⊥},
          if B.val ≤ quadraticCoordinateAnnihilator e q U.val then
            (2 : ℝ) ^ (Module.finrank (ZMod 2) U.val * Module.finrank (ZMod 2) B.val) else 0 := by
      apply Finset.sum_congr rfl
      intro U _
      rw [binary_image_noncanonical_lifts_count_quadratic π hπ κ hcentral e q hsq U.val]
      exact sum_nonzero_below_eq_indicator (quadraticCoordinateAnnihilator e q U.val)
        (fun B : Submodule (ZMod 2) (ι → ZMod 2) ↦
          (2 : ℝ) ^ (Module.finrank (ZMod 2) U.val * Module.finrank (ZMod 2) B))
    _ = ∑ B : {B : Submodule (ZMod 2) (ι → ZMod 2) // B ≠ ⊥},
        ∑ U : {U : Submodule (ZMod 2) (Fin R → ZMod 2) // FullBinaryQuotientImage e U},
          if B.val ≤ quadraticCoordinateAnnihilator e q U.val then
            (2 : ℝ) ^ (Module.finrank (ZMod 2) U.val * Module.finrank (ZMod 2) B.val) else 0 :=
      Finset.sum_comm
    _ = ∑ B : {B : Submodule (ZMod 2) (ι → ZMod 2) // B ≠ ⊥},
        ∑ U : Submodule (ZMod 2) (Fin R → ZMod 2),
          if FullBinaryQuotientImage e U then
            if B.val ≤ quadraticCoordinateAnnihilator e q U then
              (2 : ℝ) ^ (Module.finrank (ZMod 2) U * Module.finrank (ZMod 2) B.val) else 0
          else 0 := by
      apply Finset.sum_congr rfl
      intro B _
      exact sum_subtype_eq_indicator (FullBinaryQuotientImage e)
        (fun U : Submodule (ZMod 2) (Fin R → ZMod 2) ↦
          if B.val ≤ quadraticCoordinateAnnihilator e q U then
            (2 : ℝ) ^ (Module.finrank (ZMod 2) U * Module.finrank (ZMod 2) B.val) else 0)
    _ = _ := by
      unfold exceptionalQuadraticIncidence
      apply Finset.sum_congr rfl
      intro B _
      apply Finset.sum_congr rfl
      intro U _
      simp only [fullQuadraticSubspace_iff,FullBinaryQuotientImage]
      split_ifs <;> simp_all

/-- Uniform exceptional estimate for actual subgroups. The premises are
structural charts and local quadratic-form facts, not count identities. -/
theorem fullNoncanonicalBinarySubgroup_card_le {G : Type*} [Group G] [Finite G] {R : ℕ}
    [FiniteDimensional (ZMod 2) W] [Finite W]
    [∀ i, FiniteDimensional (ZMod 2) (V i)] [∀ i, Finite (V i)]
    (π : G →* Multiplicative (Fin R → ZMod 2)) (hπ : Function.Surjective π)
    (κ : Multiplicative (ι → ZMod 2) ≃* π.ker) (hcentral : π.ker ≤ Subgroup.center G)
    (e : (Fin R → ZMod 2) ≃ₗ[ZMod 2] (W × ∀ i, V i))
    (q : ∀ i, QuadraticForm (ZMod 2) (V i))
    (hsq : ∀ g : G, binarySquareCoordinate π κ g = fun i ↦ q i ((e (π g).toAdd).2 i))
    (hq : ∀ i, (q i).polarBilin.SeparatingLeft)
    (hv : ∀ i, 2 ≤ Module.finrank (ZMod 2) (V i))
    (hM : ∀ i, Nat.card ((q i).IsometryEquiv (q i)) ≤ 72) :
    (Nat.card (FullNoncanonicalBinarySubgroup π e) : ℝ) ≤
      (exceptionalGaussianConstant / eulerProduct) * (binaryGaussianSum R : ℝ) *
        (2 : ℝ)^(-((R : ℝ)/2 - Fintype.card ι)) := by
  rw [fullNoncanonicalBinarySubgroup_card_eq_incidence π hπ κ hcentral e q hsq]
  exact exceptionalQuadraticIncidence_le e q hq hv hM

end SymmetricSubgroupAsymptotics
