import SymmetricSubgroupAsymptotics.QuadraticRealization

/-!
# Exact binary hyperbolic orthogonal orders

An orthogonal automorphism is identified with the images of a hyperbolic
basis. The concrete finite computation counts pairs and orthogonal pairs
of pairs; it does not assume an automorphism order or a realization count.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace SymmetricSubgroupAsymptotics

abbrev BinaryPlane := Fin 2 → ZMod 2
abbrev BinaryFourSpace := Fin 4 → ZMod 2

def hyperbolicPolarTwo (x y : BinaryPlane) : ZMod 2 := x 0 * y 1 + x 1 * y 0

def hyperbolicPolarFour (x y : BinaryFourSpace) : ZMod 2 :=
  x 0 * y 1 + x 1 * y 0 + x 2 * y 3 + x 3 * y 2

theorem hyperbolicQuadraticTwo_polar (x y : BinaryPlane) :
    hyperbolicQuadraticTwo.polarBilin x y = hyperbolicPolarTwo x y := by
  simp only [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar,
    hyperbolicQuadraticTwo_apply, Pi.add_apply, hyperbolicPolarTwo]
  ring

theorem hyperbolicQuadraticFour_polar (x y : BinaryFourSpace) :
    hyperbolicQuadraticFour.polarBilin x y = hyperbolicPolarFour x y := by
  simp only [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar,
    hyperbolicQuadraticFour_apply, Pi.add_apply, hyperbolicPolarFour]
  ring

theorem hyperbolicQuadraticTwo_nonsingular : hyperbolicQuadraticTwo.polarBilin.SeparatingLeft := by
  intro x hx
  have h0 := hx ![0,1]
  have h1 := hx ![1,0]
  rw [hyperbolicQuadraticTwo_polar] at h0 h1
  simp [hyperbolicPolarTwo] at h0 h1
  funext i
  fin_cases i <;> assumption

theorem hyperbolicQuadraticFour_nonsingular : hyperbolicQuadraticFour.polarBilin.SeparatingLeft := by
  intro x hx
  have h0 := hx ![0,1,0,0]
  have h1 := hx ![1,0,0,0]
  have h2 := hx ![0,0,0,1]
  have h3 := hx ![0,0,1,0]
  rw [hyperbolicQuadraticFour_polar] at h0 h1 h2 h3
  simp [hyperbolicPolarFour] at h0 h1 h2 h3
  funext i
  fin_cases i <;> assumption

private theorem isometry_preserves_polar {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (q : QuadraticForm (ZMod 2) V) (e : q.IsometryEquiv q) (x y : V) :
    q.polarBilin (e x) (e y) = q.polarBilin x y := by
  simp only [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar,
    ← map_add, e.map_app]

private def selfIsometryOfPreserves {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [Finite V] (q : QuadraticForm (ZMod 2) V) (hq : q.polarBilin.SeparatingLeft)
    (f : V →ₗ[ZMod 2] V) (hpres : q.comp f = q) : q.IsometryEquiv q := by
  have hp : q.polarBilin = LinearMap.compl₁₂ q.polarBilin f f :=
    (congrArg QuadraticMap.polarBilin hpres).symm.trans (QuadraticMap.polarBilin_comp q f)
  have hk : f.ker = ⊥ := by
    ext x
    change f x = 0 ↔ x = 0
    constructor
    · intro hx
      apply hq
      intro y
      rw [hp]
      change q.polarBilin (f x) (f y) = 0
      simp [hx]
    · rintro rfl
      exact map_zero f
  have hi : Function.Injective f := LinearMap.ker_eq_bot.mp hk
  exact {
    toLinearEquiv := LinearEquiv.ofBijective f ⟨hi, Finite.surjective_of_injective hi⟩
    map_app' := fun x => congrArg (fun t : QuadraticForm (ZMod 2) V => t x) hpres }

private theorem quadratic_pair_expansion {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (q : QuadraticForm (ZMod 2) V) (a b : V) (s t : ZMod 2) :
    q (s • a + t • b) = s * s * q a + t * t * q b + s * t * q.polarBilin a b := by
  rw [QuadraticMap.map_add q]
  simp only [QuadraticMap.map_smul, ← QuadraticMap.polarBilin_apply_apply,
    LinearMap.map_smul, LinearMap.smul_apply, smul_eq_mul]
  ring

/-- All ordered hyperbolic pairs in the plane. -/
def hyperbolicFrameTwoSet : Finset (BinaryPlane × BinaryPlane) :=
  ((Finset.univ.filter (fun x => hyperbolicQuadraticTwo x = 0)).product
    (Finset.univ.filter (fun x => hyperbolicQuadraticTwo x = 0))).filter
      (fun p => hyperbolicPolarTwo p.1 p.2 = 1)

/-- All ordered hyperbolic pairs in the four-dimensional space. -/
def hyperbolicPairFourSet : Finset (BinaryFourSpace × BinaryFourSpace) :=
  ((Finset.univ.filter (fun x => hyperbolicQuadraticFour x = 0)).product
    (Finset.univ.filter (fun x => hyperbolicQuadraticFour x = 0))).filter
      (fun p => hyperbolicPolarFour p.1 p.2 = 1)

/-- Two hyperbolic pairs with every cross-pair polar value zero. -/
def hyperbolicFrameFourSet : Finset ((BinaryFourSpace × BinaryFourSpace) ×
    (BinaryFourSpace × BinaryFourSpace)) :=
  (hyperbolicPairFourSet.product hyperbolicPairFourSet).filter (fun t =>
    hyperbolicPolarFour t.1.1 t.2.1 = 0 ∧ hyperbolicPolarFour t.1.1 t.2.2 = 0 ∧
    hyperbolicPolarFour t.1.2 t.2.1 = 0 ∧ hyperbolicPolarFour t.1.2 t.2.2 = 0)

private theorem mem_hyperbolicFrameTwoSet (a b : BinaryPlane) :
    (a,b) ∈ hyperbolicFrameTwoSet ↔
      hyperbolicQuadraticTwo a = 0 ∧ hyperbolicQuadraticTwo b = 0 ∧
        hyperbolicPolarTwo a b = 1 := by
  simp [hyperbolicFrameTwoSet, and_assoc]

private theorem mem_hyperbolicPairFourSet (a b : BinaryFourSpace) :
    (a,b) ∈ hyperbolicPairFourSet ↔
      hyperbolicQuadraticFour a = 0 ∧ hyperbolicQuadraticFour b = 0 ∧
        hyperbolicPolarFour a b = 1 := by
  simp [hyperbolicPairFourSet, and_assoc]

private theorem mem_hyperbolicFrameFourSet (a b c d : BinaryFourSpace) :
    ((a,b),(c,d)) ∈ hyperbolicFrameFourSet ↔
      hyperbolicQuadraticFour a = 0 ∧ hyperbolicQuadraticFour b = 0 ∧
      hyperbolicPolarFour a b = 1 ∧ hyperbolicQuadraticFour c = 0 ∧
      hyperbolicQuadraticFour d = 0 ∧ hyperbolicPolarFour c d = 1 ∧
      hyperbolicPolarFour a c = 0 ∧ hyperbolicPolarFour a d = 0 ∧
      hyperbolicPolarFour b c = 0 ∧ hyperbolicPolarFour b d = 0 := by
  simp [hyperbolicFrameFourSet, mem_hyperbolicPairFourSet, and_assoc]

private def frameTwoLinearMap (a b : BinaryPlane) : BinaryPlane →ₗ[ZMod 2] BinaryPlane :=
  (LinearMap.proj 0).smulRight a + (LinearMap.proj 1).smulRight b

private def frameFourLinearMap (a b c d : BinaryFourSpace) :
    BinaryFourSpace →ₗ[ZMod 2] BinaryFourSpace :=
  ((LinearMap.proj 0).smulRight a + (LinearMap.proj 1).smulRight b) +
    ((LinearMap.proj 2).smulRight c + (LinearMap.proj 3).smulRight d)

private theorem frameTwo_preserves (a b : BinaryPlane) (h : (a,b) ∈ hyperbolicFrameTwoSet) :
    hyperbolicQuadraticTwo.comp (frameTwoLinearMap a b) = hyperbolicQuadraticTwo := by
  rcases (mem_hyperbolicFrameTwoSet a b).mp h with ⟨ha,hb,hab⟩
  ext x
  change hyperbolicQuadraticTwo (x 0 • a + x 1 • b) = hyperbolicQuadraticTwo x
  rw [quadratic_pair_expansion, hyperbolicQuadraticTwo_polar, ha, hb, hab]
  simp

private theorem frameFour_preserves (a b c d : BinaryFourSpace)
    (h : ((a,b),(c,d)) ∈ hyperbolicFrameFourSet) :
    hyperbolicQuadraticFour.comp (frameFourLinearMap a b c d) = hyperbolicQuadraticFour := by
  rcases (mem_hyperbolicFrameFourSet a b c d).mp h with
    ⟨ha,hb,hab,hc,hd,hcd,hac,had,hbc,hbd⟩
  ext x
  change hyperbolicQuadraticFour ((x 0 • a + x 1 • b) + (x 2 • c + x 3 • d)) =
    hyperbolicQuadraticFour x
  rw [QuadraticMap.map_add hyperbolicQuadraticFour, quadratic_pair_expansion, quadratic_pair_expansion]
  have hcross : hyperbolicQuadraticFour.polarBilin (x 0 • a + x 1 • b)
      (x 2 • c + x 3 • d) = 0 := by
    simp only [map_add, LinearMap.add_apply, LinearMap.map_smul, LinearMap.smul_apply,
      hyperbolicQuadraticFour_polar, hac, had, hbc, hbd, smul_zero, zero_add]
  rw [← QuadraticMap.polarBilin_apply_apply, hcross, hyperbolicQuadraticFour_polar,
    hyperbolicQuadraticFour_polar, ha, hb, hc, hd, hab, hcd]
  simp

private theorem binaryPlane_expand (x : BinaryPlane) :
    x = x 0 • Pi.single 0 1 + x 1 • Pi.single 1 1 := by
  ext i
  fin_cases i <;> simp

private theorem binaryFour_expand (x : BinaryFourSpace) :
    x = (x 0 • Pi.single 0 1 + x 1 • Pi.single 1 1) +
      (x 2 • Pi.single 2 1 + x 3 • Pi.single 3 1) := by
  ext i
  fin_cases i <;> simp

private theorem isometry_frameTwo_mem
    (e : hyperbolicQuadraticTwo.IsometryEquiv hyperbolicQuadraticTwo) :
    (e (Pi.single 0 1), e (Pi.single 1 1)) ∈ hyperbolicFrameTwoSet := by
  rw [mem_hyperbolicFrameTwoSet]
  simp only [QuadraticMap.IsometryEquiv.map_app, ← hyperbolicQuadraticTwo_polar,
    isometry_preserves_polar]
  decide

private theorem isometry_frameFour_mem
    (e : hyperbolicQuadraticFour.IsometryEquiv hyperbolicQuadraticFour) :
    ((e (Pi.single 0 1), e (Pi.single 1 1)),
      (e (Pi.single 2 1), e (Pi.single 3 1))) ∈ hyperbolicFrameFourSet := by
  rw [mem_hyperbolicFrameFourSet]
  simp only [QuadraticMap.IsometryEquiv.map_app, ← hyperbolicQuadraticFour_polar,
    isometry_preserves_polar]
  decide

/-- Orthogonal maps of the plane are exactly its actual hyperbolic bases. -/
def orthogonalTwoFrameEquiv :
    hyperbolicQuadraticTwo.IsometryEquiv hyperbolicQuadraticTwo ≃
      {p // p ∈ hyperbolicFrameTwoSet} where
  toFun e := ⟨(e (Pi.single 0 1), e (Pi.single 1 1)), isometry_frameTwo_mem e⟩
  invFun p := selfIsometryOfPreserves hyperbolicQuadraticTwo hyperbolicQuadraticTwo_nonsingular
    (frameTwoLinearMap p.1.1 p.1.2) (frameTwo_preserves _ _ p.2)
  left_inv e := by
    apply DFunLike.ext
    intro x
    change x 0 • e (Pi.single 0 1) + x 1 • e (Pi.single 1 1) = e x
    simpa only [map_add, map_smul] using congrArg e (binaryPlane_expand x).symm
  right_inv p := by
    rcases p with ⟨⟨a,b⟩,h⟩
    apply Subtype.ext
    change (frameTwoLinearMap a b (Pi.single 0 1), frameTwoLinearMap a b (Pi.single 1 1)) = (a,b)
    simp [frameTwoLinearMap, LinearMap.smulRight_apply]

/-- Orthogonal maps of the four-space are exactly two orthogonal hyperbolic
pairs. Nonsingularity proves that the resulting linear map is invertible. -/
def orthogonalFourFrameEquiv :
    hyperbolicQuadraticFour.IsometryEquiv hyperbolicQuadraticFour ≃
      {p // p ∈ hyperbolicFrameFourSet} where
  toFun e := ⟨((e (Pi.single 0 1), e (Pi.single 1 1)),
    (e (Pi.single 2 1), e (Pi.single 3 1))), isometry_frameFour_mem e⟩
  invFun p := selfIsometryOfPreserves hyperbolicQuadraticFour hyperbolicQuadraticFour_nonsingular
    (frameFourLinearMap p.1.1.1 p.1.1.2 p.1.2.1 p.1.2.2)
      (frameFour_preserves _ _ _ _ p.2)
  left_inv e := by
    apply DFunLike.ext
    intro x
    change (x 0 • e (Pi.single 0 1) + x 1 • e (Pi.single 1 1)) +
      (x 2 • e (Pi.single 2 1) + x 3 • e (Pi.single 3 1)) = e x
    simpa only [map_add, map_smul] using congrArg e (binaryFour_expand x).symm
  right_inv p := by
    rcases p with ⟨⟨⟨a,b⟩,⟨c,d⟩⟩,h⟩
    apply Subtype.ext
    change ((frameFourLinearMap a b c d (Pi.single 0 1), frameFourLinearMap a b c d (Pi.single 1 1)),
      (frameFourLinearMap a b c d (Pi.single 2 1), frameFourLinearMap a b c d (Pi.single 3 1))) =
        ((a,b),(c,d))
    simp [frameFourLinearMap, LinearMap.smulRight_apply]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
/-- Kernel-checked enumeration of the two actual plane frames. -/
theorem hyperbolicFrameTwoSet_card : hyperbolicFrameTwoSet.card = 2 := by decide

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
/-- Kernel-checked enumeration of the thirty-six four-space hyperbolic pairs. -/
theorem hyperbolicPairFourSet_card : hyperbolicPairFourSet.card = 36 := by decide

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
/-- Kernel-checked enumeration of the seventy-two four-space frames. -/
theorem hyperbolicFrameFourSet_card : hyperbolicFrameFourSet.card = 72 := by decide

/-- The actual orthogonal isometry group of `x₀x₁` has order two. -/
theorem hyperbolicQuadraticTwo_isometry_card :
    Nat.card (hyperbolicQuadraticTwo.IsometryEquiv hyperbolicQuadraticTwo) = 2 := by
  rw [Nat.card_congr orthogonalTwoFrameEquiv]
  simpa only [Nat.card_eq_fintype_card, Fintype.card_coe] using hyperbolicFrameTwoSet_card

/-- The actual orthogonal isometry group of `x₀x₁+x₂x₃` has order seventy-two. -/
theorem hyperbolicQuadraticFour_isometry_card :
    Nat.card (hyperbolicQuadraticFour.IsometryEquiv hyperbolicQuadraticFour) = 72 := by
  rw [Nat.card_congr orthogonalFourFrameEquiv]
  simpa only [Nat.card_eq_fintype_card, Fintype.card_coe] using hyperbolicFrameFourSet_card

/-- The dimension-two realization bound includes all degenerate source forms
and the empty fibre. -/
theorem hyperbolicTwo_realizations_le {E : Type*} [AddCommGroup E] [Module (ZMod 2) E]
    (Q : QuadraticForm (ZMod 2) E) :
    Nat.card (QuadraticRealizations Q hyperbolicQuadraticTwo) ≤ 2 := by
  exact (quadraticRealization_card_le Q hyperbolicQuadraticTwo
    hyperbolicQuadraticTwo_nonsingular).trans_eq hyperbolicQuadraticTwo_isometry_card

/-- The dimension-four realization bound used for every pivot equation. -/
theorem hyperbolicFour_realizations_le {E : Type*} [AddCommGroup E] [Module (ZMod 2) E]
    (Q : QuadraticForm (ZMod 2) E) :
    Nat.card (QuadraticRealizations Q hyperbolicQuadraticFour) ≤ 72 := by
  exact (quadraticRealization_card_le Q hyperbolicQuadraticFour
    hyperbolicQuadraticFour_nonsingular).trans_eq hyperbolicQuadraticFour_isometry_card

end SymmetricSubgroupAsymptotics
