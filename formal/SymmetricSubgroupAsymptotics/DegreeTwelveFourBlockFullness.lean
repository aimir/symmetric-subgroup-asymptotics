import SymmetricSubgroupAsymptotics.DegreeTwelveFourBlockSigns

/-!
# Full local Klein images in the original four-by-three branch

The original correlated block kernel has full A4 image on each literal
four-point fibre. Cubing a lift of a local Klein translation lands in the
intrinsic binary core, so that core has full V4 image on each fibre. There
is no assertion that the core is the independent product of those images.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace DegreeTwelveFourBlockFullness

open DegreeTwelveFourBlockCore

section Coordinates

variable {A Ω X : Type} [Group A] [MulAction A Ω] [MulAction A X]
    (b : Ω → X) (hb : ∀ (a : A) (ω : Ω), b (a • ω) = a • b ω)
    (e : ∀ x : X, Fin 4 ≃ originalBlockFibre b x)

/-- Actual ambient transport, expressed in the chosen original point charts. -/
def transition (a : A) (x : X) : Equiv.Perm (Fin 4) :=
  ((e x).trans (OriginalBlockSignCoordinates.fibreTransport b hb a x)).trans (e (a • x)).symm

@[simp] theorem transition_apply_chart (a : A) (x : X) (i : Fin 4) :
    ((e (a • x) (transition b hb e a x i) : originalBlockFibre b (a • x)) : Ω) =
      a • ((e x i : originalBlockFibre b x) : Ω) := by
  unfold transition
  simp only [Equiv.trans_apply, Equiv.apply_symm_apply]
  rfl

theorem transition_mul (a c : A) (x : X) :
    transition b hb e (a * c) x =
      transition b hb e a (c • x) * transition b hb e c x := by
  apply Equiv.ext
  intro i
  have hL := transition_apply_chart b hb e (a * c) x i
  have hC := transition_apply_chart b hb e c x i
  have hA := transition_apply_chart b hb e a (c • x) (transition b hb e c x i)
  have hx : (a * c) • x = a • (c • x) := mul_smul a c x
  have hR : ((e ((a * c) • x)
      ((transition b hb e a (c • x) * transition b hb e c x) i) :
        originalBlockFibre b ((a * c) • x)) : Ω) =
      (a * c) • ((e x i : originalBlockFibre b x) : Ω) := by
    rw [hx]
    simpa only [Equiv.Perm.mul_apply, mul_smul] using hA.trans (congrArg (fun ω => a • ω) hC)
  apply (e ((a * c) • x)).injective
  apply Subtype.ext
  exact hL.trans hR.symm

@[simp] theorem transition_one (x : X) : transition b hb e 1 x = 1 := by
  have h := transition_mul b hb e 1 1 x
  simp only [one_mul, one_smul] at h
  let t := transition b hb e 1 x
  change t = t * t at h
  change t = 1
  calc
    t = t⁻¹ * (t * t) := by simp
    _ = t⁻¹ * t := (congrArg (fun z => t⁻¹ * z) h).symm
    _ = 1 := inv_mul_cancel t

/-- Whole-ambient conjugation retains the original kernel element and
transports its literal coordinate. -/
theorem fibreCoordinate_conjugation [Finite Ω]
    (a : A) (x : X)
    (k : DegreeTwelveFourBlockCore.Kernel (A := A) (X := X)) :
    fibreCoordinate b hb e (a • x) (MulAut.conjNormal a k) =
      transition b hb e a x * fibreCoordinate b hb e x k *
        (transition b hb e a x)⁻¹ := by
  letI : ∀ x : X, Fintype (originalBlockFibre b x) := fun _ => Fintype.ofFinite _
  change (e (a • x)).symm.permCongr
      (OriginalBlockClassBound.coordinate b hb (a • x) (MulAut.conjNormal a k)) = _
  rw [OriginalBlockSignCoordinates.coordinate_conjugation]
  ext i
  simp [transition, fibreCoordinate, Equiv.Perm.mul_apply]

/-- Each coordinate of the exact original kernel, valued in A4. -/
def alternatingCoordinate (hEven : AllEven b hb e) (x : X) :
    DegreeTwelveFourBlockCore.Kernel (A := A) (X := X) →* A4 where
  toFun k := alternatingCoordinates b hb e hEven k x
  map_one' := by exact congrFun (alternatingCoordinates b hb e hEven).map_one x
  map_mul' k l := by exact congrFun ((alternatingCoordinates b hb e hEven).map_mul k l) x

theorem alternatingCoordinate_conjugation [Finite Ω]
    (hEven : AllEven b hb e) (a : A) (x : X)
    (k : DegreeTwelveFourBlockCore.Kernel (A := A) (X := X)) :
    alternatingCoordinate b hb e hEven (a • x) (MulAut.conjNormal a k) =
      MulAut.conjNormal (transition b hb e a x)
        (alternatingCoordinate b hb e hEven x k) := by
  apply Subtype.ext
  exact fibreCoordinate_conjugation b hb e a x k

end Coordinates

section FullImages

variable {A Ω X : Type} [Group A] [Finite A] [Finite Ω] [Finite X]
    [MulAction A Ω] [MulAction A X] [FaithfulSMul A Ω]
    [MulAction.IsPretransitive A Ω] [MulAction.IsPretransitive A X]
    (b : Ω → X) (hb : ∀ (a : A) (ω : Ω), b (a • ω) = a • b ω)
    (e : ∀ x : X, Fin 4 ≃ originalBlockFibre b x)

omit [Finite Ω] [MulAction.IsPretransitive A Ω] [MulAction.IsPretransitive A X] in
/-- Saturation produces a positive local normal head in an actual image.
All other local heads are retained until that witness is found. -/
theorem exists_positive_fibre_normal
    (N : Subgroup A) [N.Normal]
    (hHead : 0 < Module.finrank (ZMod 3)
      (primeRelativeCharacters 3 (N ⊓ (MulAction.toPermHom A X).ker))) :
    ∃ (x : X) (M : Subgroup (fibreCoordinate b hb e x).range) (hM : M.Normal),
      letI := hM
      0 < Module.finrank (ZMod 3) (primeRelativeCharacters 3 M) := by
  let U : X → Subgroup (Equiv.Perm (Fin 4)) := fun x => (fibreCoordinate b hb e x).range
  let ρ : ∀ x, DegreeTwelveFourBlockCore.Kernel (A := A) (X := X) →* U x :=
    fun x => (fibreCoordinate b hb e x).rangeRestrict
  have hfaithful : Function.Injective (fun k x => ρ x k) := by
    intro k l hkl
    apply OriginalBlockClassBound.coordinates_injective b hb
    funext x
    apply (e x).symm.permCongrHom.injective
    exact congrArg Subtype.val (congrFun hkl x)
  by_contra h
  have hzero : ∀ x (M : Subgroup (U x)) (hM : M.Normal),
      letI := hM
      Module.finrank (ZMod 3) (primeRelativeCharacters 3 M) = 0 := by
    intro x M hM
    letI := hM
    by_contra hz
    have hpos : 0 < Module.finrank (ZMod 3) (primeRelativeCharacters 3 M) :=
      Nat.pos_of_ne_zero hz
    exact h ⟨x, M, hM, hpos⟩
  have hz := primeRelativeHead_faithful_family_eq_zero 3 (fun x => U x) ρ
    (fun x => (fibreCoordinate b hb e x).rangeRestrict_surjective) hfaithful hzero
    (N.subgroupOf (MulAction.toPermHom A X).ker)
  have hle := primeRelativeHead_inf_le_subgroupOf 3 N (MulAction.toPermHom A X).ker
  rw [hz] at hle
  omega

/-- Every literal A4 coordinate is onto. The transport is by actual ambient
conjugation, with no independent coordinate lift assumed. -/
theorem alternatingCoordinate_surjective
    (hTop : Nat.card (MulAction.toPermHom A X).range = Nat.card X)
    (N : Subgroup A) [N.Normal]
    (hHead : 0 < Module.finrank (ZMod 3)
      (primeRelativeCharacters 3 (N ⊓ (MulAction.toPermHom A X).ker)))
    (hEven : AllEven b hb e) (x : X) :
    Function.Surjective (alternatingCoordinate b hb e hEven x) := by
  obtain ⟨x₀, M, hM, hpos⟩ := exists_positive_fibre_normal b hb e N hHead
  letI := hM
  letI : MulAction.IsPretransitive (fibreCoordinate b hb e x₀).range (Fin 4) :=
    DegreeTwelveFourBlockSigns.fibreCoordinate_pretransitive b hb e hTop x₀
  have hU := degreeFour_positive_relativeHead_eq_alternating
    (fibreCoordinate b hb e x₀).range M hpos
  have hfull : Function.Surjective (alternatingCoordinate b hb e hEven x₀) := by
    intro v
    have hv : (v : Equiv.Perm (Fin 4)) ∈ (fibreCoordinate b hb e x₀).range := by
      rw [hU]
      exact v.2
    obtain ⟨k, hk⟩ := hv
    exact ⟨k, Subtype.ext hk⟩
  obtain ⟨a, rfl⟩ := MulAction.exists_smul_eq A x₀ x
  intro v
  obtain ⟨k, hk⟩ := hfull ((MulAut.conjNormal (transition b hb e a x₀)).symm v)
  refine ⟨MulAut.conjNormal a k, ?_⟩
  rw [alternatingCoordinate_conjugation, hk, MulEquiv.apply_symm_apply]

end FullImages

section CoreCoordinates

private theorem a4_six (g : A4) : g ^ 6 = 1 := by
  decide +kernel +revert

private theorem v4_two (g : V4) : g ^ 2 = 1 := by
  have h := Monoid.pow_exponent_eq_one g
  rw [alternatingGroup.exponent_kleinFour_of_card_eq_four (by simp)] at h
  exact h

variable {G T I : Type*} [Group G] [Group T]
    (π : G →* T) (ρ : π.ker →* (I → A4)) (hρ : Function.Injective ρ)

/-- A local Klein lift can be cubed inside the original kernel. Cubing kills
all local ternary parts simultaneously but retains the chosen translation. -/
theorem coreCoordinates_surjective (i : I)
    (honto : Function.Surjective (fun k : π.ker => ρ k i)) :
    Function.Surjective (fun w : core π ρ hρ => coreCoordinates π ρ hρ w i) := by
  intro v
  obtain ⟨k, hk⟩ := honto (v : A4)
  have hk6 : k ^ 6 = 1 := by
    apply hρ
    rw [map_pow, map_one]
    funext j
    exact a4_six (ρ k j)
  let w : core π ρ hρ := ⟨(k : G) ^ 3,
    π.ker.pow_mem k.2 3, by
      have h := congrArg Subtype.val hk6
      simpa only [← pow_mul] using h⟩
  refine ⟨w, ?_⟩
  apply Subtype.ext
  change ρ (k ^ 3) i = (v : A4)
  rw [map_pow]
  change (ρ k i) ^ 3 = (v : A4)
  change ρ k i = (v : A4) at hk
  rw [hk]
  have hv : (v : A4) ^ 2 = 1 := congrArg Subtype.val (v4_two v)
  calc
    (v : A4) ^ 3 = (v : A4) ^ 2 * (v : A4) := by rw [pow_succ]
    _ = (v : A4) := by rw [hv, one_mul]

end CoreCoordinates

end DegreeTwelveFourBlockFullness

namespace OriginalMinimalBlock

variable {A Ω : Type} [Group A] [Finite A] [Finite Ω] [MulAction A Ω]
    [FaithfulSMul A Ω] [MulAction.IsPretransitive A Ω]
    {ω₀ : Ω} (D : OriginalMinimalBlock (A := A) ω₀)

/-- The intrinsic binary core has full local V4 images in every original
fibre. It may still be a proper correlated subgroup of V4 cubed. -/
theorem fourByThree_coreCoordinates_surjective
    (N : Subgroup A) [N.Normal] (c : ActualChiefSeries D.Component)
    (hPoints : Nat.card D.Points = 3) (hTopOrder : Nat.card D.Top = 3)
    (hWeight : actualChiefSeriesTernaryWeight c = 1)
    (hTop : Module.finrank (ZMod 3)
      (primeRelativeCharacters 3 (originalNormalRange D.topMap N)) = 1)
    (hRank : Module.finrank (ZMod 3) (primeRelativeCharacters 3 N) = 2)
    (e : ∀ x : D.Points, Fin 4 ≃ originalBlockFibre D.map x)
    (x : D.Points) :
    let hEven := D.fourByThree_allEven N c hPoints hTopOrder hWeight hTop hRank e
    let ρ := DegreeTwelveFourBlockCore.alternatingCoordinates D.map D.map_equivariant e hEven
    let hρ := DegreeTwelveFourBlockCore.alternatingCoordinates_injective
      D.map D.map_equivariant e hEven
    Function.Surjective (fun w : DegreeTwelveFourBlockCore.core D.topMap ρ hρ =>
      DegreeTwelveFourBlockCore.coreCoordinates D.topMap ρ hρ w x) := by
  dsimp only
  apply DegreeTwelveFourBlockFullness.coreCoordinates_surjective
  have hHead := D.fourByThree_intersection_head_eq_one N c hPoints hWeight hTop hRank
  exact DegreeTwelveFourBlockFullness.alternatingCoordinate_surjective D.map D.map_equivariant e
    (hTopOrder.trans hPoints.symm) N (by rw [hHead]; norm_num) _ x

end OriginalMinimalBlock
end SymmetricSubgroupAsymptotics
