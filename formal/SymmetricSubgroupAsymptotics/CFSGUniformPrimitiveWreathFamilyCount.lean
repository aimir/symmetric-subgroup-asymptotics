import SymmetricSubgroupAsymptotics.CFSGActualPrimitiveWreathLargeLocal
import SymmetricSubgroupAsymptotics.ActualFullWreathFiniteLocalMenuSubquadratic

/-! Uniform actual primitive-local full-component family count.
The large-local and finite-local estimates are produced from CFSG.
The literal local/top menus are MAXIMIZED, never summed; the count of
transitive tops is reserved for the single recursive global factor. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGUniformPrimitiveWreathFamilyCount
open ActualFullWreathFamily

local instance subgroupFinite {G : Type} [Group G] [Finite G] : Finite (Subgroup G) :=
  Finite.of_injective (fun K : Subgroup G => (K : Set G)) SetLike.coe_injective

abbrev PrimitiveLocal (r : ℕ) :=
  {R : Subgroup (Equiv.Perm (Fin r)) // MulAction.IsPreprimitive R (Fin r)}

abbrev TransitiveTop (t : ℕ) :=
  {Q : Subgroup (Equiv.Perm (Fin t)) // MulAction.IsPretransitive Q (Fin t)}

local instance primitiveLocalFintype (r : ℕ) : Fintype (PrimitiveLocal r) := Fintype.ofFinite _
local instance transitiveTopFintype (t : ℕ) : Fintype (TransitiveTop t) := Fintype.ofFinite _

def familyMaximum (r t : ℕ) : ℕ := max 1
  (Finset.univ.sup (fun R : PrimitiveLocal r =>
    Finset.univ.sup (fun Q : TransitiveTop t => Nat.card (Family R.val Q.val (Fin t)))))

theorem one_le_familyMaximum (r t : ℕ) : 1 ≤ familyMaximum r t := le_max_left _ _

theorem family_card_le_maximum {r t : ℕ} (R : Subgroup (Equiv.Perm (Fin r)))
    (hR : MulAction.IsPreprimitive R (Fin r)) (Q : Subgroup (Equiv.Perm (Fin t)))
    (hQ : MulAction.IsPretransitive Q (Fin t)) :
    Nat.card (Family R Q (Fin t)) ≤ familyMaximum r t := by
  let i : PrimitiveLocal r := ⟨R,hR⟩
  let j : TransitiveTop t := ⟨Q,hQ⟩
  have hfirst : Nat.card (Family R Q (Fin t)) ≤
      Finset.univ.sup (fun U : TransitiveTop t => Nat.card (Family i.val U.val (Fin t))) :=
    Finset.le_sup (f := fun U : TransitiveTop t => Nat.card (Family i.val U.val (Fin t)))
      (Finset.mem_univ j)
  have hsecond : Finset.univ.sup (fun U : TransitiveTop t => Nat.card (Family i.val U.val (Fin t))) ≤
      Finset.univ.sup (fun V : PrimitiveLocal r =>
        Finset.univ.sup (fun U : TransitiveTop t => Nat.card (Family V.val U.val (Fin t)))) :=
    Finset.le_sup (f := fun V : PrimitiveLocal r =>
      Finset.univ.sup (fun U : TransitiveTop t => Nat.card (Family V.val U.val (Fin t))))
      (Finset.mem_univ i)
  exact (hfirst.trans hsecond).trans (le_max_right _ _)

theorem uniform_family_count (hCFSG : CFSG.CFSGClassification) (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ r t : ℕ, 2 ≤ r → 2 ≤ t → N ≤ r*t →
      ∀ R : Subgroup (Equiv.Perm (Fin r)), MulAction.IsPreprimitive R (Fin r) →
      ∀ Q : Subgroup (Equiv.Perm (Fin t)), MulAction.IsPretransitive Q (Fin t) →
      (Nat.card (Family R Q (Fin t)) : ℝ) ≤ (2 : ℝ)^(ε*((r*t : ℕ) : ℝ)^2) := by
  obtain ⟨R₀,hR₀⟩ := CFSGActualPrimitiveWreathLargeLocal.uniform_large_local hCFSG ε hε
  let Rbound := max 2 R₀
  obtain ⟨T₀,hT₀⟩ := ActualFullWreathFiniteLocalMenuSubquadratic.bounded_permutation_locals
    hCFSG Rbound ε hε
  let Tbound := max 2 T₀
  refine ⟨Rbound*Tbound,?_⟩
  intro r t hr ht hn R hR Q hQ
  by_cases hlocal : Rbound ≤ r
  · letI : MulAction.IsPreprimitive R (Fin r) := hR
    letI : Nontrivial (Fin r) := Finite.one_lt_card_iff_nontrivial.mp
      (by simpa only [Nat.card_fin] using (show 1 < r by omega))
    have hrlarge : R₀ ≤ Nat.card (Fin r) := by
      simpa only [Nat.card_fin] using (le_max_right 2 R₀).trans hlocal
    have hrlarge2 : 2 ≤ Nat.card (Fin r) := by simpa only [Nat.card_fin] using hr
    simpa only [Nat.card_fin] using
      hR₀ (R := R) (X := Fin r) hrlarge hrlarge2 t ht Q hQ
  · have hsmall : r < Rbound := Nat.lt_of_not_ge hlocal
    have htop : Tbound ≤ t := by
      by_contra hsmallT
      have hh : r*t < Rbound*Tbound :=
        (Nat.mul_lt_mul_of_pos_right hsmall (by omega : 0 < t)).trans
          (Nat.mul_lt_mul_of_pos_left (Nat.lt_of_not_ge hsmallT)
            (by have hh := le_max_left 2 R₀; omega : 0 < Rbound))
      omega
    letI : MulAction.IsPretransitive Q (Fin t) := hQ
    have htlarge : T₀ ≤ Nat.card (Fin t) := by
      simpa only [Nat.card_fin] using (le_max_right 2 T₀).trans htop
    have hh := hT₀ r hsmall.le R Q (Fin t) htlarge
    have hh' : (Nat.card (Family R Q (Fin t)) : ℝ) ≤ (2 : ℝ)^(ε*(t : ℝ)^2) := by
      simpa only [Nat.card_fin] using hh
    have hexp : (t : ℝ)^2 ≤ ((r*t : ℕ) : ℝ)^2 := by
      exact_mod_cast Nat.pow_le_pow_left (Nat.le_mul_of_pos_left t (by omega : 0 < r)) 2
    exact hh'.trans (Real.rpow_le_rpow_of_exponent_le (by norm_num)
      (mul_le_mul_of_nonneg_left hexp hε.le))

private theorem cast_sup_le {J : Type} [DecidableEq J] (s : Finset J) (f : J → ℕ)
    (M : ℝ) (hM : 0 ≤ M) :
    (∀ j ∈ s,(f j : ℝ) ≤ M) → ((s.sup f : ℕ) : ℝ) ≤ M := by
  induction s using Finset.induction_on with
  | empty =>
      intro _
      simpa only [Finset.sup_empty,Nat.bot_eq_zero,Nat.cast_zero] using hM
  | @insert j s hj ih =>
      intro h
      rw [Finset.sup_insert]
      change ((max (f j) (s.sup f) : ℕ) : ℝ) ≤ M
      rw [Nat.cast_max]
      exact max_le (h j (Finset.mem_insert_self _ _))
        (ih (fun i hi => h i (Finset.mem_insert_of_mem hi)))

theorem familyMaximum_uniform (hCFSG : CFSG.CFSGClassification) (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ r t : ℕ, 2 ≤ r → 2 ≤ t → N ≤ r*t →
      (familyMaximum r t : ℝ) ≤ (2 : ℝ)^(ε*((r*t : ℕ) : ℝ)^2) := by
  obtain ⟨N,hN⟩ := uniform_family_count hCFSG ε hε
  refine ⟨N,?_⟩
  intro r t hr ht hn
  have hpositive : (0 : ℝ) ≤ (2 : ℝ)^(ε*((r*t : ℕ) : ℝ)^2) := by positivity
  have hone : (1 : ℝ) ≤ (2 : ℝ)^(ε*((r*t : ℕ) : ℝ)^2) :=
    Real.one_le_rpow (by norm_num) (mul_nonneg hε.le (sq_nonneg _))
  unfold familyMaximum
  rw [Nat.cast_max,Nat.cast_one]
  refine max_le hone (cast_sup_le Finset.univ
    (fun R : PrimitiveLocal r => Finset.univ.sup
      (fun Q : TransitiveTop t => Nat.card (Family R.val Q.val (Fin t)))) _ hpositive ?_)
  intro R _
  apply cast_sup_le Finset.univ
    (fun Q : TransitiveTop t => Nat.card (Family R.val Q.val (Fin t))) _ hpositive
  intro Q _
  exact hN r t hr ht hn R.val R.property Q.val Q.property

end SymmetricSubgroupAsymptotics.CFSGUniformPrimitiveWreathFamilyCount
