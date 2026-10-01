import SymmetricSubgroupAsymptotics.Non2PreE7SmallFactorModel
import SymmetricSubgroupAsymptotics.Non2PreE7A4WreathC2Group
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.LinearAlgebra.Matrix.Notation

/-!
# `GL₂(3)` and `SL₂(3)` on the eight nonzero vectors

The actual groups are the invertible and unimodular `2 × 2` matrices over
`F₃`, acting on the eight nonzero vectors of `F₃²`.  The action on the four
lines maps `GL₂(3)` onto `S₄` and `SL₂(3)` onto `A₄`, with central kernel
`{±I}` of order two.  Every nontrivial normal subgroup contains `-I`: if it
is not central, its image contains the Klein subgroup, and the matrices over
`(12)(34)` square to `-I`.

All finite facts are checked by `decide` on the literal matrices.
-/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics
namespace LinearThree

open Equiv NaturalS4

abbrev M2 := Matrix (Fin 2) (Fin 2) (ZMod 3)
abbrev V2 := Fin 2 → ZMod 3
abbrev GL3 := Matrix.GeneralLinearGroup (Fin 2) (ZMod 3)

/-- The determinant of a `2 × 2` matrix. -/
def det2 (A : M2) : ZMod 3 := A 0 0 * A 1 1 - A 0 1 * A 1 0

/-- The literal invertible matrices. -/
def glSet : Finset M2 := Finset.univ.filter (fun A => det2 A ≠ 0)

theorem det_eq_det2 (A : M2) : A.det = det2 A := Matrix.det_fin_two A

theorem coe_mem_glSet (g : GL3) : (g : M2) ∈ glSet := by
  rw [glSet, Finset.mem_filter, ← det_eq_det2]
  exact ⟨Finset.mem_univ _, Matrix.GeneralLinearGroup.det_ne_zero g⟩

/-- The invertible matrix of a literal matrix with nonzero determinant. -/
def ofGL (A : M2) (h : A ∈ glSet) : GL3 :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero A (by
    rw [det_eq_det2]
    exact (Finset.mem_filter.mp h).2)

@[simp] theorem coe_ofGL (A : M2) (h : A ∈ glSet) : ((ofGL A h : GL3) : M2) = A := rfl

/-! ## The four lines -/

/-- The index of the line through a nonzero vector. -/
def lineOf (v : V2) : Fin 4 :=
  if v 0 = 0 then 1 else if v 1 = 0 then 0 else if v 1 = v 0 then 2 else 3

/-- A spanning vector of each line. -/
def lineRep : Fin 4 → V2 := ![![1, 0], ![0, 1], ![1, 1], ![1, 2]]

/-- The action of a matrix on the four lines. -/
def lineFun (A : M2) (ℓ : Fin 4) : Fin 4 := lineOf (A.mulVec (lineRep ℓ))

set_option maxRecDepth 100000 in
theorem lineFun_mul : ∀ A ∈ glSet, ∀ B ∈ glSet, ∀ ℓ : Fin 4,
    lineFun (A * B) ℓ = lineFun A (lineFun B ℓ) := by decide +kernel

theorem lineFun_one : ∀ ℓ : Fin 4, lineFun 1 ℓ = ℓ := by decide

/-- The projective action `GL₂(3) → S₄`. -/
def projective : GL3 →* Perm (Fin 4) where
  toFun g :=
    { toFun := lineFun g
      invFun := lineFun (↑g⁻¹ : M2)
      left_inv := fun ℓ => by
        rw [← lineFun_mul _ (coe_mem_glSet g⁻¹) _ (coe_mem_glSet g), Units.inv_mul,
          lineFun_one]
      right_inv := fun ℓ => by
        rw [← lineFun_mul _ (coe_mem_glSet g) _ (coe_mem_glSet g⁻¹), Units.mul_inv,
          lineFun_one] }
  map_one' := by
    refine Equiv.ext fun ℓ => ?_
    show lineFun ((1 : GL3) : M2) ℓ = ℓ
    rw [Units.val_one, lineFun_one]
  map_mul' g h := by
    refine Equiv.ext fun ℓ => ?_
    show lineFun ((g * h : GL3) : M2) ℓ = lineFun g (lineFun h ℓ)
    rw [Units.val_mul, lineFun_mul _ (coe_mem_glSet g) _ (coe_mem_glSet h)]

theorem projective_apply (g : GL3) (ℓ : Fin 4) : projective g ℓ = lineFun g ℓ := rfl

set_option maxRecDepth 100000 in
theorem lineFun_trivial_iff : ∀ A ∈ glSet, (∀ ℓ : Fin 4, lineFun A ℓ = ℓ) ↔ (A = 1 ∨ A = -1) := by
  decide +kernel

theorem mem_ker_projective (g : GL3) :
    g ∈ projective.ker ↔ (g : M2) = 1 ∨ (g : M2) = -1 := by
  rw [MonoidHom.mem_ker, ← lineFun_trivial_iff _ (coe_mem_glSet g)]
  constructor
  · intro h ℓ
    have := congrArg (fun σ : Perm (Fin 4) => σ ℓ) h
    simpa [projective_apply] using this
  · intro h
    ext ℓ
    simp [projective_apply, h ℓ]

set_option maxRecDepth 100000 in
theorem lineFun_onto : ∀ τ : Perm (Fin 4), ∃ A ∈ glSet, ∀ ℓ : Fin 4, lineFun A ℓ = τ ℓ := by
  decide +kernel

theorem projective_surjective : Function.Surjective projective := by
  intro τ
  obtain ⟨A, hA, hAτ⟩ := lineFun_onto τ
  exact ⟨ofGL A hA, by ext ℓ; simp [projective_apply, hAτ ℓ]⟩

set_option maxRecDepth 100000 in
theorem sq_of_c1 : ∀ A ∈ glSet, (∀ ℓ : Fin 4, lineFun A ℓ = c1 ℓ) → A * A = -1 := by decide +kernel

theorem central_of_ker (z : GL3) (hz : z ∈ projective.ker) (g : GL3) : z * g = g * z := by
  rcases (mem_ker_projective z).mp hz with h | h <;>
    · apply Units.ext
      simp [h]

/-- The nontrivial element of the central kernel. -/
theorem eq_of_ker_ne_one {x y : GL3} (hx : x ∈ projective.ker) (hy : y ∈ projective.ker)
    (hx1 : x ≠ 1) (hy1 : y ≠ 1) : x = y := by
  have hx' : (x : M2) = -1 := by
    rcases (mem_ker_projective x).mp hx with h | h
    · exact absurd (Units.ext h) hx1
    · exact h
  have hy' : (y : M2) = -1 := by
    rcases (mem_ker_projective y).mp hy with h | h
    · exact absurd (Units.ext h) hy1
    · exact h
  exact Units.ext (hx'.trans hy'.symm)

/-- Every nontrivial normal subgroup of `GL₂(3)` contains the centre `{±I}`. -/
theorem normal_cover (N : Subgroup GL3) (hN : N.Normal) (hNb : N ≠ ⊥) :
    projective.ker ≤ N := by
  have hneg : ∃ g ∈ N, (g : M2) = -1 := by
    by_cases hmap : N.map projective = ⊥
    · obtain ⟨⟨g, hgN⟩, hg1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hNb
      have hg1' : g ≠ 1 := fun h => hg1 (Subtype.ext h)
      have hgker : g ∈ projective.ker := by
        rw [MonoidHom.mem_ker]
        have : projective g ∈ N.map projective := ⟨g, hgN, rfl⟩
        rw [hmap] at this
        exact (Subgroup.mem_bot).mp this
      rcases (mem_ker_projective g).mp hgker with h | h
      · exact absurd (Units.ext h) hg1'
      · exact ⟨g, hgN, h⟩
    · haveI : (N.map projective).Normal := hN.map _ projective_surjective
      have hk := le_of_minimal_selfCentralizing klein klein_minimal klein_selfCentralizing
        (N.map projective) hmap
      obtain ⟨g, hgN, hg⟩ := hk (show c1 ∈ klein by decide)
      refine ⟨g * g, N.mul_mem hgN hgN, ?_⟩
      rw [Units.val_mul]
      exact sq_of_c1 _ (coe_mem_glSet g) (fun ℓ => by rw [← hg]; rfl)
  obtain ⟨g, hgN, hg⟩ := hneg
  intro x hx
  rcases (mem_ker_projective x).mp hx with h | h
  · rw [show x = 1 from Units.ext h]
    exact N.one_mem
  · rw [show x = g from Units.ext (h.trans hg.symm)]
    exact hgN

theorem card_ker_projective : Nat.card projective.ker = 2 ^ 1 := by
  have hneg : -1 ∈ glSet := by decide
  let m : GL3 := ofGL (-1) hneg
  have hm : m ∈ projective.ker := (mem_ker_projective m).mpr (Or.inr rfl)
  have hm1 : m ≠ 1 := by
    intro h
    have := congrArg (fun g : GL3 => (g : M2)) h
    simp only [m, coe_ofGL, Units.val_one] at this
    revert this
    decide
  rw [pow_one, Nat.card_eq_two_iff]
  refine ⟨1, ⟨m, hm⟩, fun h => hm1 (congrArg Subtype.val h).symm, ?_⟩
  ext ⟨x, hx⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_univ, iff_true]
  by_cases hx1 : x = 1
  · left
    exact Subtype.ext hx1
  · right
    exact Subtype.ext (eq_of_ker_ne_one hx hm hx1 hm1)

/-! ## The nonzero vectors -/

/-- The eight nonzero vectors of `F₃²`. -/
abbrev NV := {v : V2 // v ≠ 0}

theorem inv_mulVec_mulVec (g : GL3) (v : V2) :
    (↑g⁻¹ : M2).mulVec ((g : M2).mulVec v) = v := by
  rw [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]

theorem mulVec_inv_mulVec (g : GL3) (v : V2) :
    (g : M2).mulVec ((↑g⁻¹ : M2).mulVec v) = v := by
  rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]

theorem mulVec_ne_zero (g : GL3) (v : V2) (hv : v ≠ 0) : (g : M2).mulVec v ≠ 0 := by
  intro h
  apply hv
  rw [← inv_mulVec_mulVec g v, h, Matrix.mulVec_zero]

/-- The natural action on the nonzero vectors. -/
def natural : GL3 →* Perm NV where
  toFun g :=
    { toFun := fun v => ⟨(g : M2).mulVec v, mulVec_ne_zero g v v.2⟩
      invFun := fun v => ⟨(↑g⁻¹ : M2).mulVec v, mulVec_ne_zero g⁻¹ v v.2⟩
      left_inv := fun v => Subtype.ext (inv_mulVec_mulVec g v)
      right_inv := fun v => Subtype.ext (mulVec_inv_mulVec g v) }
  map_one' := by
    refine Equiv.ext fun v => Subtype.ext ?_
    show ((1 : GL3) : M2).mulVec v = v
    rw [Units.val_one, Matrix.one_mulVec]
  map_mul' g h := by
    refine Equiv.ext fun v => Subtype.ext ?_
    show ((g * h : GL3) : M2).mulVec v = (g : M2).mulVec ((h : M2).mulVec v)
    rw [Units.val_mul, Matrix.mulVec_mulVec]

set_option maxRecDepth 100000 in
theorem fixes_all_iff : ∀ A ∈ glSet, (∀ v : V2, v ≠ 0 → A.mulVec v = v) → A = 1 := by decide +kernel

theorem natural_injective : Function.Injective natural := by
  rw [injective_iff_map_eq_one]
  intro g hg
  apply Units.ext
  apply fixes_all_iff _ (coe_mem_glSet g)
  intro v hv
  have := congrArg (fun σ : Perm NV => ((σ ⟨v, hv⟩ : NV) : V2)) hg
  exact this

theorem card_NV : Nat.card NV = 8 := by
  rw [Nat.card_eq_fintype_card]
  decide

/-! ## The special linear group -/

/-- The literal unimodular matrices. -/
def slSet : Finset M2 := Finset.univ.filter (fun A => det2 A = 1)

/-- `SL₂(3)` inside `GL₂(3)`. -/
def slSub : Subgroup GL3 := Matrix.GeneralLinearGroup.det.ker

theorem mem_slSub (g : GL3) : g ∈ slSub ↔ (g : M2) ∈ slSet := by
  rw [slSub, MonoidHom.mem_ker, slSet, Finset.mem_filter, ← det_eq_det2, Units.ext_iff]
  simp [Matrix.GeneralLinearGroup.det]

abbrev SL3 := ↥slSub

set_option maxRecDepth 100000 in
theorem lineFun_sl_mem_a4 : ∀ A ∈ slSet, ∃ σ ∈ a4Set, ∀ ℓ : Fin 4, lineFun A ℓ = σ ℓ := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem lineFun_sl_onto : ∀ σ ∈ a4Set, ∃ A ∈ slSet, ∀ ℓ : Fin 4, lineFun A ℓ = σ ℓ := by
  decide +kernel

theorem slSet_sub : ∀ A ∈ slSet, A ∈ glSet := by decide

/-- The projective action `SL₂(3) → A₄`. -/
def projectiveSL : SL3 →* a4 :=
  (projective.comp slSub.subtype).codRestrict a4 (fun g => by
    obtain ⟨σ, hσ, hA⟩ := lineFun_sl_mem_a4 _ ((mem_slSub g).mp g.2)
    have : projective (slSub.subtype g) = σ := by
      ext ℓ
      simp [projective_apply, hA ℓ]
    simp only [MonoidHom.comp_apply]
    rw [this]
    exact hσ)

theorem projectiveSL_surjective : Function.Surjective projectiveSL := by
  rintro ⟨σ, hσ⟩
  obtain ⟨A, hA, hAσ⟩ := lineFun_sl_onto σ hσ
  let g : GL3 := ofGL A (slSet_sub A hA)
  have hg : g ∈ slSub := (mem_slSub g).mpr hA
  refine ⟨⟨g, hg⟩, Subtype.ext ?_⟩
  ext ℓ
  simp [projectiveSL, projective_apply, g, hAσ ℓ]

theorem mem_ker_projectiveSL (g : SL3) :
    g ∈ projectiveSL.ker ↔ (g : GL3) ∈ projective.ker := by
  rw [MonoidHom.mem_ker, MonoidHom.mem_ker, projectiveSL, Subtype.ext_iff]
  rfl

theorem central_of_kerSL (z : SL3) (hz : z ∈ projectiveSL.ker) (g : SL3) : z * g = g * z :=
  Subtype.ext (central_of_ker _ ((mem_ker_projectiveSL z).mp hz) g)

end LinearThree
end SymmetricSubgroupAsymptotics
