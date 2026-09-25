import SymmetricSubgroupAsymptotics.CriticalActionModels
import SymmetricSubgroupAsymptotics.HyperbolicFrames
import SymmetricSubgroupAsymptotics.RetainedQuadraticAnnihilator
import SymmetricSubgroupAsymptotics.PhysicalExceptionalBound

/-!
# Concrete products of critical actions

The binary choice is false for D8 and true for E8. All regular C2/V4 factors
are retained in a free binary factor. The nonabelian factors, their physical
projection maps, and their original central square coordinates remain explicit.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace SymmetricSubgroupAsymptotics

def criticalFactorHalfRank (b : Bool) : ℕ := if b then 2 else 1
def criticalFactorRank (b : Bool) : ℕ := if b then 4 else 2

abbrev CriticalFactorSpace (b : Bool) := Fin (criticalFactorRank b) → ZMod 2

/-- Original translation/shear coordinates in interleaved physical order. -/
def criticalFactorChart (b : Bool) :
    ((Fin (criticalFactorHalfRank b) → ZMod 2) ×
      (Fin (criticalFactorHalfRank b) → ZMod 2)) ≃ₗ[ZMod 2] CriticalFactorSpace b := by
  cases b
  · exact d8QuotientChart
  · exact e8QuotientChart

def criticalFactorQuadratic (b : Bool) : QuadraticForm (ZMod 2) (CriticalFactorSpace b) := by
  cases b
  · exact hyperbolicQuadraticTwo
  · exact hyperbolicQuadraticFour

@[simp] theorem criticalFactorChart_zero (b : Bool) : criticalFactorChart b (0, 0) = 0 :=
  (criticalFactorChart b).map_zero

theorem criticalFactorChart_quadratic (b : Bool)
    (v : (Fin (criticalFactorHalfRank b) → ZMod 2) ×
      (Fin (criticalFactorHalfRank b) → ZMod 2)) :
    criticalFactorQuadratic b (criticalFactorChart b v) = binaryDot v.2 v.1 := by
  cases b
  · exact d8QuotientChart_quadratic v
  · exact e8QuotientChart_quadratic v

theorem criticalFactorQuadratic_nonsingular (b : Bool) :
    (criticalFactorQuadratic b).polarBilin.SeparatingLeft := by
  cases b
  · exact hyperbolicQuadraticTwo_nonsingular
  · exact hyperbolicQuadraticFour_nonsingular

theorem criticalFactorSpace_finrank_ge_two (b : Bool) :
    2 ≤ Module.finrank (ZMod 2) (CriticalFactorSpace b) := by
  simp only [Module.finrank_pi, Fintype.card_fin]
  cases b <;> decide

theorem criticalFactorQuadratic_isometry_card_le (b : Bool) :
    Nat.card ((criticalFactorQuadratic b).IsometryEquiv (criticalFactorQuadratic b)) ≤ 72 := by
  cases b
  · change Nat.card (hyperbolicQuadraticTwo.IsometryEquiv hyperbolicQuadraticTwo) ≤ 72
    rw [hyperbolicQuadraticTwo_isometry_card]
    decide
  · change Nat.card (hyperbolicQuadraticFour.IsometryEquiv hyperbolicQuadraticFour) ≤ 72
    rw [hyperbolicQuadraticFour_isometry_card]

variable {ι : Type*} [Fintype ι]

/-- An actual finite direct product, before choosing any quotient basis. -/
abbrev CriticalProductGroup (a : ℕ) (d : ι → Bool) :=
  Multiplicative (Fin a → ZMod 2) × ∀ i, BinaryHeisenberg (criticalFactorHalfRank (d i))

abbrev CriticalProductSpace (a : ℕ) (d : ι → Bool) :=
  (Fin a → ZMod 2) × ∀ i, CriticalFactorSpace (d i)

def criticalProductRank (a : ℕ) (d : ι → Bool) : ℕ := a + ∑ i, criticalFactorRank (d i)

theorem criticalProductSpace_finrank (a : ℕ) (d : ι → Bool) :
    Module.finrank (ZMod 2) (CriticalProductSpace a d) = criticalProductRank a d := by
  simp [CriticalProductSpace, criticalProductRank, Module.finrank_prod,
    Module.finrank_pi_fintype]

/-- A proved dimension chart; it is not an assumed physical square chart. -/
def criticalProductChart (a : ℕ) (d : ι → Bool) :
    (Fin (criticalProductRank a d) → ZMod 2) ≃ₗ[ZMod 2] CriticalProductSpace a d :=
  LinearEquiv.ofFinrankEq _ _ (by
    rw [Module.finrank_pi, Fintype.card_fin]
    exact (criticalProductSpace_finrank a d).symm)

/-- Projection to each actual nonabelian direct factor. -/
def criticalProductFactorProjection (a : ℕ) (d : ι → Bool) (i : ι) :
    CriticalProductGroup a d →* BinaryHeisenberg (criticalFactorHalfRank (d i)) where
  toFun g := g.2 i
  map_one' := rfl
  map_mul' _ _ := rfl

omit [Fintype ι] in
theorem criticalProductFactorProjection_surjective (a : ℕ) (d : ι → Bool) (i : ι) :
    Function.Surjective (criticalProductFactorProjection a d i) := by
  classical
  intro g
  exact ⟨(1, Function.update (fun _ ↦ 1) i g), by simp [criticalProductFactorProjection]⟩

/-- The original quotient, expressed in the proved finite-dimensional basis. -/
def criticalProductQuotient (a : ℕ) (d : ι → Bool) :
    CriticalProductGroup a d →* Multiplicative (Fin (criticalProductRank a d) → ZMod 2) where
  toFun g := Multiplicative.ofAdd ((criticalProductChart a d).symm
    (g.1.toAdd, fun i ↦ criticalFactorChart (d i) ((g.2 i).a, (g.2 i).b)))
  map_one' := by
    change Multiplicative.ofAdd ((criticalProductChart a d).symm
      (0, fun i ↦ criticalFactorChart (d i) (0, 0))) = 1
    simp
    rfl
  map_mul' g h := by
    apply Multiplicative.toAdd.injective
    change (criticalProductChart a d).symm
      (g.1.toAdd + h.1.toAdd, fun i ↦ criticalFactorChart (d i)
        ((g.2 i).a + (h.2 i).a, (g.2 i).b + (h.2 i).b)) =
      (criticalProductChart a d).symm
        (g.1.toAdd, fun i ↦ criticalFactorChart (d i) ((g.2 i).a, (g.2 i).b)) +
      (criticalProductChart a d).symm
        (h.1.toAdd, fun i ↦ criticalFactorChart (d i) ((h.2 i).a, (h.2 i).b))
    rw [← (criticalProductChart a d).symm.map_add]
    apply congrArg (criticalProductChart a d).symm
    apply Prod.ext
    · rfl
    · funext i
      exact (criticalFactorChart (d i)).map_add
        ((g.2 i).a, (g.2 i).b) ((h.2 i).a, (h.2 i).b)

theorem criticalProductQuotient_chart (a : ℕ) (d : ι → Bool) (g : CriticalProductGroup a d) :
    criticalProductChart a d ((criticalProductQuotient a d g).toAdd) =
      (g.1.toAdd, fun i ↦ criticalFactorChart (d i) ((g.2 i).a, (g.2 i).b)) :=
  (criticalProductChart a d).apply_symm_apply _

theorem criticalProductQuotient_surjective (a : ℕ) (d : ι → Bool) :
    Function.Surjective (criticalProductQuotient a d) := by
  intro v
  let w := criticalProductChart a d v.toAdd
  refine ⟨(Multiplicative.ofAdd w.1, fun i ↦
    ⟨((criticalFactorChart (d i)).symm (w.2 i)).1,
      ((criticalFactorChart (d i)).symm (w.2 i)).2, 0⟩), ?_⟩
  apply Multiplicative.toAdd.injective
  apply (criticalProductChart a d).injective
  rw [criticalProductQuotient_chart]
  dsimp [w]
  ext i j <;> simp

theorem mem_criticalProductQuotient_ker (a : ℕ) (d : ι → Bool)
    (g : CriticalProductGroup a d) :
    g ∈ (criticalProductQuotient a d).ker ↔
      g.1 = 1 ∧ ∀ i, (g.2 i).a = 0 ∧ (g.2 i).b = 0 := by
  change criticalProductQuotient a d g = 1 ↔ _
  constructor
  · intro hg
    have he := congrArg (fun v ↦ criticalProductChart a d v.toAdd) hg
    change criticalProductChart a d (criticalProductQuotient a d g).toAdd =
      criticalProductChart a d 0 at he
    rw [criticalProductQuotient_chart] at he
    have he' : (g.1.toAdd, fun i ↦ criticalFactorChart (d i) ((g.2 i).a, (g.2 i).b)) = 0 := by
      simpa using he
    refine ⟨?_, fun i ↦ ?_⟩
    · exact Multiplicative.toAdd.injective (congrArg Prod.fst he')
    · have hi := congrFun (congrArg Prod.snd he') i
      have hi' : ((g.2 i).a, (g.2 i).b) = 0 :=
        (criticalFactorChart (d i)).injective (by simpa using hi)
      exact Prod.mk.inj hi'
  · rintro ⟨hw, hg⟩
    apply Multiplicative.toAdd.injective
    apply (criticalProductChart a d).injective
    rw [criticalProductQuotient_chart]
    simp [hw, (hg _).1, (hg _).2]
    rfl

/-- The original kernel chart is the tuple of actual central coordinates. -/
def criticalProductKernelChart (a : ℕ) (d : ι → Bool) :
    Multiplicative (ι → ZMod 2) ≃* (criticalProductQuotient a d).ker where
  toFun z := ⟨(1, fun i ↦ BinaryHeisenberg.central _ (Multiplicative.ofAdd (z.toAdd i))),
    (mem_criticalProductQuotient_ker a d _).mpr ⟨rfl, fun _ ↦ ⟨rfl, rfl⟩⟩⟩
  invFun g := Multiplicative.ofAdd (fun i ↦ (g.1.2 i).c)
  left_inv _ := rfl
  right_inv g := by
    apply Subtype.ext
    rcases (mem_criticalProductQuotient_ker a d g.1).mp g.2 with ⟨hw, hg⟩
    apply Prod.ext
    · exact hw.symm
    · funext i
      apply BinaryHeisenberg.ext <;> simp [BinaryHeisenberg.central, (hg i).1, (hg i).2]
  map_mul' z w := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · funext i
      exact (BinaryHeisenberg.central _).map_mul _ _

theorem criticalProductQuotient_ker_central (a : ℕ) (d : ι → Bool) :
    (criticalProductQuotient a d).ker ≤ Subgroup.center (CriticalProductGroup a d) := by
  intro g hg
  rcases (mem_criticalProductQuotient_ker a d g).mp hg with ⟨hw, hgi⟩
  rw [Subgroup.mem_center_iff]
  intro h
  apply Prod.ext
  · simp [hw]
  · funext i
    exact Subgroup.mem_center_iff.mp
      (BinaryHeisenberg.quotient_ker_central _
        ((BinaryHeisenberg.mem_quotient_ker _).mpr (hgi i))) (h.2 i)

/-- The square equation uses the tuple of original central coordinates. -/
theorem criticalProduct_square_coordinate (a : ℕ) (d : ι → Bool)
    (g : CriticalProductGroup a d) :
    binarySquareCoordinate (criticalProductQuotient a d) (criticalProductKernelChart a d) g =
      fun i ↦ criticalFactorQuadratic (d i)
        ((criticalProductChart a d (criticalProductQuotient a d g).toAdd).2 i) := by
  rw [criticalProductQuotient_chart]
  funext i
  rw [criticalFactorChart_quadratic]
  change ((g.2 i) ^ 2).c = binaryDot (g.2 i).b (g.2 i).a
  rw [BinaryHeisenberg.square]
  rfl

/-- Literal noncanonical subgroups, full on every actual nonabelian factor.
The regular binary factor is unrestricted, so imposing any further C2/V4
projection conditions selects a subfamily of this one. -/
def CriticalProductNoncanonicalFull (a : ℕ) (d : ι → Bool) :=
  {H : Subgroup (CriticalProductGroup a d) //
    ¬ (criticalProductQuotient a d).ker ≤ H ∧
      ∀ i, H.map (criticalProductFactorProjection a d i) = ⊤}

/-- Actual full factor projections imply fullness of the actual quotient
image, using the explicit physical projection maps and original charts. -/
theorem criticalProduct_full_quotient_image (a : ℕ) (d : ι → Bool)
    (H : Subgroup (CriticalProductGroup a d))
    (hfull : ∀ i, H.map (criticalProductFactorProjection a d i) = ⊤) :
    ∃ U : Submodule (ZMod 2) (Fin (criticalProductRank a d) → ZMod 2),
      H.map (criticalProductQuotient a d) = U.toAddSubgroup.toSubgroup ∧
        FullBinaryQuotientImage (criticalProductChart a d) U := by
  let U := (binarySubmoduleSubgroupOrderIso (criticalProductRank a d)).symm
    (H.map (criticalProductQuotient a d))
  have hU : H.map (criticalProductQuotient a d) = U.toAddSubgroup.toSubgroup :=
    ((binarySubmoduleSubgroupOrderIso (criticalProductRank a d)).apply_symm_apply _).symm
  refine ⟨U, hU, ?_⟩
  intro i v
  let g₀ : BinaryHeisenberg (criticalFactorHalfRank (d i)) :=
    ⟨((criticalFactorChart (d i)).symm v).1, ((criticalFactorChart (d i)).symm v).2, 0⟩
  have hg₀ : g₀ ∈ H.map (criticalProductFactorProjection a d i) := by
    rw [hfull i]
    exact Subgroup.mem_top _
  obtain ⟨g, hg, hgi⟩ := hg₀
  have hm : (criticalProductQuotient a d g).toAdd ∈ U := by
    change criticalProductQuotient a d g ∈ U.toAddSubgroup.toSubgroup
    rw [← hU]
    exact ⟨g, hg, rfl⟩
  refine ⟨⟨(criticalProductQuotient a d g).toAdd, hm⟩, ?_⟩
  change (criticalProductChart a d (criticalProductQuotient a d g).toAdd).2 i = v
  rw [criticalProductQuotient_chart]
  change g.2 i = g₀ at hgi
  change criticalFactorChart (d i) ((g.2 i).a, (g.2 i).b) = v
  rw [hgi]
  exact (criticalFactorChart (d i)).apply_symm_apply v

/-- The concrete products satisfy every structural premise of the general
exceptional theorem; none of those premises is assumed by this corollary. -/
theorem criticalProduct_quotient_noncanonical_card_le (a : ℕ) (d : ι → Bool) :
    (Nat.card (FullNoncanonicalBinarySubgroup (criticalProductQuotient a d)
      (criticalProductChart a d)) : ℝ) ≤
      (exceptionalGaussianConstant / eulerProduct) *
        (binaryGaussianSum (criticalProductRank a d) : ℝ) *
          (2 : ℝ) ^ (-((criticalProductRank a d : ℝ) / 2 - Fintype.card ι)) := by
  exact fullNoncanonicalBinarySubgroup_card_le
    (criticalProductQuotient a d) (criticalProductQuotient_surjective a d)
    (criticalProductKernelChart a d) (criticalProductQuotient_ker_central a d)
    (criticalProductChart a d) (fun i ↦ criticalFactorQuadratic (d i))
    (criticalProduct_square_coordinate a d)
    (fun i ↦ criticalFactorQuadratic_nonsingular (d i))
    (fun i ↦ criticalFactorSpace_finrank_ge_two (d i))
    (fun i ↦ criticalFactorQuadratic_isometry_card_le (d i))

/-- Uniform bound for literal subgroups with full actual D8/E8 projections.
The count is over original subgroups, without duplicated quotient-image data. -/
theorem criticalProduct_noncanonical_full_card_le (a : ℕ) (d : ι → Bool) :
    (Nat.card (CriticalProductNoncanonicalFull a d) : ℝ) ≤
      (exceptionalGaussianConstant / eulerProduct) *
        (binaryGaussianSum (criticalProductRank a d) : ℝ) *
          (2 : ℝ) ^ (-((criticalProductRank a d : ℝ) / 2 - Fintype.card ι)) := by
  have hle : Nat.card (CriticalProductNoncanonicalFull a d) ≤
      Nat.card (FullNoncanonicalBinarySubgroup (criticalProductQuotient a d)
        (criticalProductChart a d)) := by
    apply Nat.card_le_card_of_injective
      (fun H : CriticalProductNoncanonicalFull a d ↦
        (⟨H.1, H.2.1, criticalProduct_full_quotient_image a d H.1 H.2.2⟩ :
          FullNoncanonicalBinarySubgroup (criticalProductQuotient a d)
            (criticalProductChart a d)))
    intro H K h
    exact Subtype.ext (congrArg (fun L : FullNoncanonicalBinarySubgroup
      (criticalProductQuotient a d) (criticalProductChart a d) ↦ L.val) h)
  exact (show (Nat.card (CriticalProductNoncanonicalFull a d) : ℝ) ≤
    (Nat.card (FullNoncanonicalBinarySubgroup (criticalProductQuotient a d)
      (criticalProductChart a d)) : ℝ) by exact_mod_cast hle).trans
        (criticalProduct_quotient_noncanonical_card_le a d)

end SymmetricSubgroupAsymptotics
