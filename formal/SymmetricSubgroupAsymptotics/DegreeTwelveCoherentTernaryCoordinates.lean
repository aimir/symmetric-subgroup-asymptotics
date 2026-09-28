import SymmetricSubgroupAsymptotics.DegreeTwelvePrimeBaseReduction
import SymmetricSubgroupAsymptotics.TernaryA4InvariantSubmodules

/-!
# Coherent ternary coordinates over the original natural A4 top

If all signs of the actual block kernel vanish, a lift of an A4 point
stabilizer acts evenly on its original three-point fibre: its cube is in
the block kernel. Transporting one fibre chart by actual ambient elements
therefore gives charts whose every transition is even. In these charts,
ambient conjugation permutes the literal kernel coordinates without signs.

No complement of the block kernel, quotient section, or independence of
the ternary coordinates is assumed. In particular the coordinate map below
is an injection of the original kernel, not a replacement by a full product.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace DegreeTwelveCoherentTernaryCoordinates

open OriginalBlockSignCoordinates DegreeThreeBlockInversionHead

private theorem alternating_four_fixed_cube :
    ∀ (g : Equiv.Perm (Fin 4)) (i : Fin 4),
      g ∈ alternatingGroup (Fin 4) → g i = i → g ^ 3 = 1 := by
  change ∀ (g : Equiv.Perm (Fin 4)) (i : Fin 4),
    Equiv.Perm.sign g = 1 → g i = i → g ^ 3 = 1
  decide +kernel

variable {A Ω X : Type} [Group A] [MulAction A Ω] [MulAction A X]
variable (b : Ω → X) (hb : ∀ (a : A) (ω : Ω), b (a • ω) = a • b ω)

/-- An actual lift of a stabilizer element in the natural four-point A4
top has its cube in the original block kernel. -/
theorem stabilizer_cube_mem_kernel
    (hTop : IsNaturalA4Action (OriginalBlockClassBound.Top (A := A) (X := X)) X)
    (a : A) (x : X) (ha : a • x = x) :
    a ^ 3 ∈ OriginalBlockClassBound.Kernel (A := A) (X := X) := by
  obtain ⟨r, hr⟩ := hTop
  let t : OriginalBlockClassBound.Top (A := A) (X := X) :=
    (MulAction.toPermHom A X).rangeRestrict a
  have ht : labelledActionHom r t ∈ alternatingGroup (Fin 4) := by
    rw [← hr]
    exact ⟨t, rfl⟩
  have hfix : labelledActionHom r t (r x) = r x := by
    rw [labelledActionHom_apply]
    exact congrArg r ha
  have hc := alternating_four_fixed_cube (labelledActionHom r t) (r x) ht hfix
  rw [← map_pow] at hc
  change MulAction.toPermHom A X (a ^ 3) = 1
  apply Equiv.ext
  intro y
  have hy := congrArg (fun g : Equiv.Perm (Fin 4) => g (r y)) hc
  change labelledActionHom r (t ^ 3) (r y) = r y at hy
  rw [labelledActionHom_apply] at hy
  change r (((t ^ 3 : OriginalBlockClassBound.Top (A := A) (X := X)) :
    Equiv.Perm X) y) = r y at hy
  have htPow : ((t ^ 3 : OriginalBlockClassBound.Top (A := A) (X := X)) :
      Equiv.Perm X) = MulAction.toPermHom A X (a ^ 3) := by
    rw [map_pow]
    rfl
  rw [htPow] at hy
  exact r.injective hy

variable [∀ x : X, Fintype (originalBlockFibre b x)]

/-- The whole original fibre stabilizer acts evenly, although it need not
be contained in the block kernel. This is the untwisting step. -/
theorem stabilizer_sign_eq_one
    (hTop : IsNaturalA4Action (OriginalBlockClassBound.Top (A := A) (X := X)) X)
    (hSigns : coordinateSigns b hb = 1)
    (x : X) (s : MulAction.stabilizer A x) :
    Equiv.Perm.sign (originalBlockFibreAction b hb x s) = 1 := by
  let k : OriginalBlockClassBound.Kernel (A := A) (X := X) :=
    ⟨(s : A) ^ 3, stabilizer_cube_mem_kernel hTop (s : A) x s.2⟩
  have hk : coordinateSign b hb x k = 1 :=
    congrFun (DFunLike.congr_fun hSigns k) x
  have hc : OriginalBlockClassBound.coordinate b hb x k =
      (originalBlockFibreAction b hb x s) ^ 3 := by
    rw [← map_pow]
    rfl
  have hs : Equiv.Perm.sign (originalBlockFibreAction b hb x s) ^ 3 = 1 := by
    have h := (permutationBinarySign_eq_one (originalBlockFibre b x) _).mp hk
    rw [hc, map_pow] at h
    have hsign : Equiv.Perm.sign (originalBlockFibreAction b hb x s) =
        @Equiv.Perm.sign (originalBlockFibre b x)
          (fun u v => Classical.propDecidable (u = v)) _
          (originalBlockFibreAction b hb x s) := by
      exact @Equiv.Perm.sign_eq_sign_of_equiv
        (originalBlockFibre b x) inferInstance (originalBlockFibre b x) inferInstance
        (fun u v => Classical.propDecidable (u = v)) inferInstance
        (originalBlockFibreAction b hb x s) (originalBlockFibreAction b hb x s)
        (Equiv.refl _) (fun _ => rfl)
    rw [hsign]
    exact h
  have hcube : ∀ z : ℤˣ, z ^ 3 = z := by
    intro z
    rcases Int.units_eq_one_or z with rfl | rfl <;> decide
  rwa [hcube] at hs

section TransportedCharts

variable [MulAction.IsPretransitive A X]
variable (x₀ : X) (e₀ : Fin 3 ≃ originalBlockFibre b x₀)

private def transporter (x : X) : A :=
  Classical.choose (MulAction.exists_smul_eq A x₀ x)

private theorem transporter_spec (x : X) : transporter (A := A) x₀ x • x₀ = x :=
  Classical.choose_spec (MulAction.exists_smul_eq A x₀ x)

/-- Each chart is obtained by an actual ambient transporter from one
original fibre. It retains the original point map, including its inverse. -/
def coherentChart (x : X) : Fin 3 ≃ originalBlockFibre b x where
  toFun i := ⟨transporter (A := A) x₀ x • (e₀ i).1, by
    rw [hb, (e₀ i).2, transporter_spec]⟩
  invFun ω := e₀.symm ⟨(transporter (A := A) x₀ x)⁻¹ • ω.1, by
    rw [hb, ω.2]
    calc
      (transporter (A := A) x₀ x)⁻¹ • x =
          (transporter (A := A) x₀ x)⁻¹ •
            (transporter (A := A) x₀ x • x₀) :=
        congrArg (fun y : X => (transporter (A := A) x₀ x)⁻¹ • y)
          (transporter_spec (A := A) x₀ x).symm
      _ = x₀ := inv_smul_smul _ _⟩
  left_inv i := by
    apply e₀.injective
    rw [e₀.apply_symm_apply]
    exact Subtype.ext (inv_smul_smul _ _)
  right_inv ω := by
    apply Subtype.ext
    change transporter (A := A) x₀ x •
      (e₀ (e₀.symm ⟨(transporter (A := A) x₀ x)⁻¹ • ω.1, _⟩)).1 = ω.1
    rw [e₀.apply_symm_apply]
    exact smul_inv_smul _ _

/-- Relabel the actual transport between two fibres, in the chosen charts. -/
def transition (e : ∀ x : X, Fin 3 ≃ originalBlockFibre b x)
    (a : A) (x : X) : OddMarkerGroup :=
  ((e x).trans (fibreTransport b hb a x)).trans (e (a • x)).symm

/-- Every transition of the transported charts is even. Thus the original
monomial action has been untwisted by an explicit family of point charts. -/
theorem coherentChart_transition_sign
    (hTop : IsNaturalA4Action (OriginalBlockClassBound.Top (A := A) (X := X)) X)
    (hSigns : coordinateSigns b hb = 1) (a : A) (x : X) :
    oddMarkerSign (transition b hb (coherentChart b hb x₀ e₀) a x) = 1 := by
  let s : MulAction.stabilizer A x₀ :=
    ⟨(transporter (A := A) x₀ (a • x))⁻¹ * a * transporter (A := A) x₀ x, by
      change ((transporter (A := A) x₀ (a • x))⁻¹ * a *
        transporter (A := A) x₀ x) • x₀ = x₀
      rw [mul_smul, mul_smul, transporter_spec]
      calc
        (transporter (A := A) x₀ (a • x))⁻¹ • (a • x) =
            (transporter (A := A) x₀ (a • x))⁻¹ •
              (transporter (A := A) x₀ (a • x) • x₀) :=
          congrArg (fun y : X => (transporter (A := A) x₀ (a • x))⁻¹ • y)
            (transporter_spec (A := A) x₀ (a • x)).symm
        _ = x₀ := inv_smul_smul _ _⟩
  have he : transition b hb (coherentChart b hb x₀ e₀) a x =
      e₀.symm.permCongr (originalBlockFibreAction b hb x₀ s) := by
    apply Equiv.ext
    intro i
    change (coherentChart b hb x₀ e₀ (a • x)).symm
        (fibreTransport b hb a x (coherentChart b hb x₀ e₀ x i)) =
      e₀.symm (originalBlockFibreAction b hb x₀ s (e₀ i))
    apply e₀.injective
    change e₀ (e₀.symm ⟨(transporter (A := A) x₀ (a • x))⁻¹ •
        (a • (transporter (A := A) x₀ x • (e₀ i).1)), _⟩) =
      e₀ (e₀.symm ⟨((transporter (A := A) x₀ (a • x))⁻¹ * a *
        transporter (A := A) x₀ x) • (e₀ i).1, _⟩)
    rw [e₀.apply_symm_apply, e₀.apply_symm_apply]
    apply Subtype.ext
    simp only [mul_smul]
  apply (oddMarkerSign_eq_one _).mpr
  rw [he, Equiv.Perm.sign_permCongr]
  exact stabilizer_sign_eq_one b hb hTop hSigns x₀ s

end TransportedCharts

/-- Coherence is an equation on actual point-chart transitions; it is not
an assumption that the original extension splits. -/
def Coherent (e : ∀ x : X, Fin 3 ≃ originalBlockFibre b x) : Prop :=
  ∀ (a : A) (x : X), oddMarkerSign (transition b hb e a x) = 1

theorem exists_coherent_charts [MulAction.IsPretransitive A X]
    (x₀ : X) (e₀ : Fin 3 ≃ originalBlockFibre b x₀)
    (hTop : IsNaturalA4Action (OriginalBlockClassBound.Top (A := A) (X := X)) X)
    (hSigns : coordinateSigns b hb = 1) :
    ∃ e : ∀ x : X, Fin 3 ≃ originalBlockFibre b x, Coherent b hb e :=
  ⟨coherentChart b hb x₀ e₀,
    coherentChart_transition_sign b hb x₀ e₀ hTop hSigns⟩

/-- The literal even permutation coordinate on the whole original kernel. -/
def kernelPermutationCoordinate
    (e : ∀ x : X, Fin 3 ≃ originalBlockFibre b x)
    (hSigns : coordinateSigns b hb = 1) (x : X) :
    OriginalBlockClassBound.Kernel (A := A) (X := X) →* oddMarkerSign.ker :=
  (relabeledCoordinate (hb := hb) b e x).codRestrict oddMarkerSign.ker (fun k => by
    change oddMarkerSign (relabeledCoordinate (hb := hb) b e x k) = 1
    rw [relabeledCoordinate_sign]
    exact congrFun (DFunLike.congr_fun hSigns k) x)

def kernelTernaryCoordinate
    (e : ∀ x : X, Fin 3 ≃ originalBlockFibre b x)
    (hSigns : coordinateSigns b hb = 1) (x : X) :
    OriginalBlockClassBound.Kernel (A := A) (X := X) →* Multiplicative (ZMod 3) :=
  OddMarkerTernaryChart.chart.symm.toMonoidHom.comp
    (kernelPermutationCoordinate b hb e hSigns x)

theorem relabeledCoordinate_ambient_conjugation
    (e : ∀ x : X, Fin 3 ≃ originalBlockFibre b x)
    (a : A) (x : X) (k : OriginalBlockClassBound.Kernel (A := A) (X := X)) :
    relabeledCoordinate (hb := hb) b e (a • x) (MulAut.conjNormal a k) =
      transition b hb e a x * relabeledCoordinate (hb := hb) b e x k *
        (transition b hb e a x)⁻¹ := by
  change (e (a • x)).symm.permCongr
      (OriginalBlockClassBound.coordinate b hb (a • x) (MulAut.conjNormal a k)) =
    transition b hb e a x *
      ((e x).symm.permCongr (OriginalBlockClassBound.coordinate b hb x k)) *
        (transition b hb e a x)⁻¹
  rw [coordinate_conjugation]
  apply Equiv.ext
  intro i
  simp only [transition, Equiv.permCongr_apply,
    Equiv.Perm.mul_apply, Equiv.Perm.inv_def, Equiv.trans_apply,
    Equiv.symm_trans_apply, Equiv.symm_symm, Equiv.apply_symm_apply]

/-- With coherent charts, ambient conjugation simply transports the
actual ternary coordinate. The equation involves every original a and k. -/
theorem kernelTernaryCoordinate_conjugation
    (e : ∀ x : X, Fin 3 ≃ originalBlockFibre b x)
    (hSigns : coordinateSigns b hb = 1) (he : Coherent b hb e)
    (a : A) (x : X) (k : OriginalBlockClassBound.Kernel (A := A) (X := X)) :
    kernelTernaryCoordinate b hb e hSigns (a • x) (MulAut.conjNormal a k) =
      kernelTernaryCoordinate b hb e hSigns x k := by
  have hp : kernelPermutationCoordinate b hb e hSigns (a • x)
      (MulAut.conjNormal a k) =
      MulAut.conjNormal (transition b hb e a x)
        (kernelPermutationCoordinate b hb e hSigns x k) := by
    apply Subtype.ext
    exact relabeledCoordinate_ambient_conjugation b hb e a x k
  apply Multiplicative.toAdd.injective
  change (OddMarkerTernaryChart.chart.symm
      (kernelPermutationCoordinate b hb e hSigns (a • x)
        (MulAut.conjNormal a k))).toAdd =
    (OddMarkerTernaryChart.chart.symm
      (kernelPermutationCoordinate b hb e hSigns x k)).toAdd
  rw [hp, OddMarkerTernaryChart.chart_symm_conjugate, he a x,
    OddMarkerTernaryChart.signScalar_one, one_mul]

/-- Joint coordinates preserve the literal original kernel and all its
correlations, using faithfulness only here. -/
theorem kernelTernaryCoordinates_injective [FaithfulSMul A Ω]
    (e : ∀ x : X, Fin 3 ≃ originalBlockFibre b x)
    (hSigns : coordinateSigns b hb = 1) :
    Function.Injective (fun k x => kernelTernaryCoordinate b hb e hSigns x k) := by
  intro k l h
  apply OriginalBlockClassBound.coordinates_injective b hb
  funext x
  apply (e x).symm.permCongrHom.injective
  have hx := congrFun h x
  have hp := OddMarkerTernaryChart.chart.symm.injective hx
  exact congrArg Subtype.val hp

/-- Four labelled additive coordinates on the same actual kernel. -/
def kernelCoordinates (r : X ≃ Fin 4)
    (e : ∀ x : X, Fin 3 ≃ originalBlockFibre b x)
    (hSigns : coordinateSigns b hb = 1) :
    OriginalBlockClassBound.Kernel (A := A) (X := X) →*
      Multiplicative (Fin 4 → ZMod 3) where
  toFun k := Multiplicative.ofAdd (fun i =>
    (kernelTernaryCoordinate b hb e hSigns (r.symm i) k).toAdd)
  map_one' := by
    apply Multiplicative.toAdd.injective
    funext i
    exact congrArg Multiplicative.toAdd
      (map_one (kernelTernaryCoordinate b hb e hSigns (r.symm i)))
  map_mul' k l := by
    apply Multiplicative.toAdd.injective
    funext i
    exact congrArg Multiplicative.toAdd
      (map_mul (kernelTernaryCoordinate b hb e hSigns (r.symm i)) k l)

theorem kernelCoordinates_injective [FaithfulSMul A Ω]
    (r : X ≃ Fin 4) (e : ∀ x : X, Fin 3 ≃ originalBlockFibre b x)
    (hSigns : coordinateSigns b hb = 1) :
    Function.Injective (kernelCoordinates b hb r e hSigns) := by
  intro k l h
  apply kernelTernaryCoordinates_injective b hb e hSigns
  funext x
  apply Multiplicative.toAdd.injective
  have hx := congrFun (congrArg Multiplicative.toAdd h) (r x)
  change (kernelTernaryCoordinate b hb e hSigns (r.symm (r x)) k).toAdd =
    (kernelTernaryCoordinate b hb e hSigns (r.symm (r x)) l).toAdd at hx
  simpa only [r.symm_apply_apply] using hx

/-- Restriction to an actual subgroup of the original kernel. In the
retained-head application this is precisely `N ⊓ ker(top)`. -/
def subgroupCoordinates (r : X ≃ Fin 4)
    (e : ∀ x : X, Fin 3 ≃ originalBlockFibre b x)
    (hSigns : coordinateSigns b hb = 1)
    (L : Subgroup A) (hL : L ≤ OriginalBlockClassBound.Kernel (A := A) (X := X)) :
    L →* Multiplicative (Fin 4 → ZMod 3) :=
  (kernelCoordinates b hb r e hSigns).comp (Subgroup.inclusion hL)

/-- Literal range submodule; this preserves every correlation in L. -/
def coordinateImage (r : X ≃ Fin 4)
    (e : ∀ x : X, Fin 3 ≃ originalBlockFibre b x)
    (hSigns : coordinateSigns b hb = 1)
    (L : Subgroup A) (hL : L ≤ OriginalBlockClassBound.Kernel (A := A) (X := X)) :
    Submodule (ZMod 3) (Fin 4 → ZMod 3) :=
  AddSubgroup.toZModSubmodule 3 (Subgroup.toAddSubgroup'
    (subgroupCoordinates b hb r e hSigns L hL).range)

@[simp] theorem mem_coordinateImage (r : X ≃ Fin 4)
    (e : ∀ x : X, Fin 3 ≃ originalBlockFibre b x)
    (hSigns : coordinateSigns b hb = 1)
    (L : Subgroup A) (hL : L ≤ OriginalBlockClassBound.Kernel (A := A) (X := X))
    (v : Fin 4 → ZMod 3) :
    v ∈ coordinateImage b hb r e hSigns L hL ↔
      ∃ l : L, subgroupCoordinates b hb r e hSigns L hL l =
        Multiplicative.ofAdd v := Iff.rfl

theorem subgroupCoordinates_conjugation (r : X ≃ Fin 4)
    (e : ∀ x : X, Fin 3 ≃ originalBlockFibre b x)
    (hSigns : coordinateSigns b hb = 1) (he : Coherent b hb e)
    (L : Subgroup A) [L.Normal]
    (hL : L ≤ OriginalBlockClassBound.Kernel (A := A) (X := X))
    (a : A) (l : L) :
    (subgroupCoordinates b hb r e hSigns L hL (MulAut.conjNormal a l)).toAdd =
      TernaryA4InvariantSubmodules.coordinateAction (labelledActionHom r a)
        (subgroupCoordinates b hb r e hSigns L hL l).toAdd := by
  funext i
  let x : X := a⁻¹ • r.symm i
  have hx : a • x = r.symm i := smul_inv_smul a (r.symm i)
  have hi : r (a • x) = i := hx ▸ r.apply_symm_apply i
  have hj : (labelledActionHom r a).symm i = r x := by
    apply (labelledActionHom r a).injective
    rw [Equiv.apply_symm_apply, labelledActionHom_apply, hi]
  change (kernelTernaryCoordinate b hb e hSigns (r.symm i)
      (MulAut.conjNormal a (⟨(l : A), hL l.2⟩ :
        OriginalBlockClassBound.Kernel (A := A) (X := X)))).toAdd =
    (kernelTernaryCoordinate b hb e hSigns
      (r.symm ((labelledActionHom r a).symm i))
      (⟨(l : A), hL l.2⟩ : OriginalBlockClassBound.Kernel (A := A) (X := X))).toAdd
  rw [hj, r.symm_apply_apply, ← hx]
  exact congrArg Multiplicative.toAdd
    (kernelTernaryCoordinate_conjugation b hb e hSigns he a x _)

/-- Every original normal subgroup inside the kernel gives an invariant
submodule for the actual natural A4 action, once the top is labelled. -/
theorem coordinateImage_invariant (r : X ≃ Fin 4)
    (hr : labelledActionImage (A := A) r = alternatingGroup (Fin 4))
    (e : ∀ x : X, Fin 3 ≃ originalBlockFibre b x)
    (hSigns : coordinateSigns b hb = 1) (he : Coherent b hb e)
    (L : Subgroup A) [L.Normal]
    (hL : L ≤ OriginalBlockClassBound.Kernel (A := A) (X := X)) :
    TernaryA4InvariantSubmodules.Invariant (coordinateImage b hb r e hSigns L hL) := by
  intro g hg v hv
  change g ∈ alternatingGroup (Fin 4) at hg
  rw [← hr] at hg
  obtain ⟨a, rfl⟩ := hg
  obtain ⟨l, hl⟩ := (mem_coordinateImage b hb r e hSigns L hL v).mp hv
  apply (mem_coordinateImage b hb r e hSigns L hL _).mpr
  refine ⟨MulAut.conjNormal a l, ?_⟩
  apply Multiplicative.toAdd.injective
  rw [subgroupCoordinates_conjugation b hb r e hSigns he L hL a l]
  exact congrArg (TernaryA4InvariantSubmodules.coordinateAction (labelledActionHom r a))
    (congrArg Multiplicative.toAdd hl)

/-- The retained intersection image is literally contained in the whole
kernel image; no independent coordinate product is introduced. -/
theorem coordinateImage_le_kernelImage (r : X ≃ Fin 4)
    (e : ∀ x : X, Fin 3 ≃ originalBlockFibre b x)
    (hSigns : coordinateSigns b hb = 1)
    (L : Subgroup A) (hL : L ≤ OriginalBlockClassBound.Kernel (A := A) (X := X)) :
    coordinateImage b hb r e hSigns L hL ≤
      coordinateImage b hb r e hSigns
        (OriginalBlockClassBound.Kernel (A := A) (X := X)) le_rfl := by
  intro v hv
  obtain ⟨l, hl⟩ := (mem_coordinateImage b hb r e hSigns L hL v).mp hv
  exact (mem_coordinateImage b hb r e hSigns _ le_rfl v).mpr
    ⟨⟨(l : A), hL l.2⟩, hl⟩

private def imageRangeEquiv (r : X ≃ Fin 4)
    (e : ∀ x : X, Fin 3 ≃ originalBlockFibre b x)
    (hSigns : coordinateSigns b hb = 1)
    (L : Subgroup A) (hL : L ≤ OriginalBlockClassBound.Kernel (A := A) (X := X)) :
    Multiplicative (coordinateImage b hb r e hSigns L hL) ≃*
      (subgroupCoordinates b hb r e hSigns L hL).range where
  toFun v := ⟨Multiplicative.ofAdd v.toAdd.1, v.toAdd.2⟩
  invFun v := Multiplicative.ofAdd ⟨v.1.toAdd, v.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

/-- Exact reconstruction equivalence for each original kernel subgroup. -/
def coordinateImageEquiv [FaithfulSMul A Ω] (r : X ≃ Fin 4)
    (e : ∀ x : X, Fin 3 ≃ originalBlockFibre b x)
    (hSigns : coordinateSigns b hb = 1)
    (L : Subgroup A) (hL : L ≤ OriginalBlockClassBound.Kernel (A := A) (X := X)) :
    L ≃* Multiplicative (coordinateImage b hb r e hSigns L hL) :=
  (MonoidHom.ofInjective (show Function.Injective
    (subgroupCoordinates b hb r e hSigns L hL) from
      (kernelCoordinates_injective b hb r e hSigns).comp
        (Subgroup.inclusion_injective hL))).trans
    (imageRangeEquiv b hb r e hSigns L hL).symm

@[simp] theorem coordinateImageEquiv_val [FaithfulSMul A Ω]
    (r : X ≃ Fin 4) (e : ∀ x : X, Fin 3 ≃ originalBlockFibre b x)
    (hSigns : coordinateSigns b hb = 1)
    (L : Subgroup A) (hL : L ≤ OriginalBlockClassBound.Kernel (A := A) (X := X))
    (l : L) :
    (coordinateImageEquiv b hb r e hSigns L hL l).toAdd.1 =
      (subgroupCoordinates b hb r e hSigns L hL l).toAdd := rfl

/-- An actual original character becomes a linear functional on precisely
the coordinate image, via the reconstruction equivalence. -/
def imageFunctional [FaithfulSMul A Ω] (r : X ≃ Fin 4)
    (e : ∀ x : X, Fin 3 ≃ originalBlockFibre b x)
    (hSigns : coordinateSigns b hb = 1)
    (L : Subgroup A) [L.Normal]
    (hL : L ≤ OriginalBlockClassBound.Kernel (A := A) (X := X))
    (χ : primeRelativeCharacters 3 L) :
    coordinateImage b hb r e hSigns L hL →ₗ[ZMod 3] ZMod 3 :=
  AddMonoidHom.toZModLinearMap 3
    (χ.1.comp (coordinateImageEquiv b hb r e hSigns L hL).symm.toMonoidHom.toAdditiveRight)

@[simp] theorem imageFunctional_apply [FaithfulSMul A Ω]
    (r : X ≃ Fin 4) (e : ∀ x : X, Fin 3 ≃ originalBlockFibre b x)
    (hSigns : coordinateSigns b hb = 1)
    (L : Subgroup A) [L.Normal]
    (hL : L ≤ OriginalBlockClassBound.Kernel (A := A) (X := X))
    (χ : primeRelativeCharacters 3 L) (l : L) :
    imageFunctional b hb r e hSigns L hL χ
        (coordinateImageEquiv b hb r e hSigns L hL l).toAdd =
      χ.1 (Additive.ofMul l) := by
  change χ.1 (Additive.ofMul
    ((coordinateImageEquiv b hb r e hSigns L hL).symm
      (coordinateImageEquiv b hb r e hSigns L hL l))) = _
  rw [MulEquiv.symm_apply_apply]

theorem imageFunctional_ne_zero [FaithfulSMul A Ω]
    (r : X ≃ Fin 4) (e : ∀ x : X, Fin 3 ≃ originalBlockFibre b x)
    (hSigns : coordinateSigns b hb = 1)
    (L : Subgroup A) [L.Normal]
    (hL : L ≤ OriginalBlockClassBound.Kernel (A := A) (X := X))
    (χ : primeRelativeCharacters 3 L) (hχ : χ ≠ 0) :
    imageFunctional b hb r e hSigns L hL χ ≠ 0 := by
  intro hf
  apply hχ
  apply Subtype.ext
  apply AddMonoidHom.ext
  intro l
  have h := DFunLike.congr_fun hf
    (coordinateImageEquiv b hb r e hSigns L hL l.toMul).toAdd
  simpa only [imageFunctional_apply, LinearMap.zero_apply] using h

theorem imageFunctional_invariant [FaithfulSMul A Ω]
    (r : X ≃ Fin 4)
    (hr : labelledActionImage (A := A) r = alternatingGroup (Fin 4))
    (e : ∀ x : X, Fin 3 ≃ originalBlockFibre b x)
    (hSigns : coordinateSigns b hb = 1) (he : Coherent b hb e)
    (L : Subgroup A) [L.Normal]
    (hL : L ≤ OriginalBlockClassBound.Kernel (A := A) (X := X))
    (χ : primeRelativeCharacters 3 L) :
    TernaryA4InvariantSubmodules.FunctionalInvariant
      (coordinateImage b hb r e hSigns L hL)
      (imageFunctional b hb r e hSigns L hL χ) := by
  intro g hg v w hgw
  change g ∈ alternatingGroup (Fin 4) at hg
  rw [← hr] at hg
  obtain ⟨a, rfl⟩ := hg
  let E := coordinateImageEquiv b hb r e hSigns L hL
  let l : L := E.symm (Multiplicative.ofAdd v)
  have hv : (E l).toAdd = v := congrArg Multiplicative.toAdd
    (E.apply_symm_apply (Multiplicative.ofAdd v))
  have hw : (E (MulAut.conjNormal a l)).toAdd = w := by
    apply Subtype.ext
    change (subgroupCoordinates b hb r e hSigns L hL (MulAut.conjNormal a l)).toAdd = w.1
    rw [subgroupCoordinates_conjugation b hb r e hSigns he L hL a l]
    change TernaryA4InvariantSubmodules.coordinateAction (labelledActionHom r a)
      (E l).toAdd.1 = w.1
    rw [hv]
    exact hgw
  calc
    imageFunctional b hb r e hSigns L hL χ w =
        χ.1 (Additive.ofMul (MulAut.conjNormal a l)) := by
      rw [← hw]
      exact imageFunctional_apply b hb r e hSigns L hL χ _
    _ = χ.1 (Additive.ofMul l) := χ.2 a l
    _ = imageFunctional b hb r e hSigns L hL χ v := by
      rw [← hv]
      exact (imageFunctional_apply b hb r e hSigns L hL χ l).symm

/-- The explicit original relative character supplies the exact invariant
head needed by the four-coordinate classifier. -/
theorem coordinateImage_hasInvariantHead [FaithfulSMul A Ω]
    (r : X ≃ Fin 4)
    (hr : labelledActionImage (A := A) r = alternatingGroup (Fin 4))
    (e : ∀ x : X, Fin 3 ≃ originalBlockFibre b x)
    (hSigns : coordinateSigns b hb = 1) (he : Coherent b hb e)
    (L : Subgroup A) [L.Normal]
    (hL : L ≤ OriginalBlockClassBound.Kernel (A := A) (X := X))
    (χ : primeRelativeCharacters 3 L) (hχ : χ ≠ 0) :
    TernaryA4InvariantSubmodules.HasInvariantHead
      (coordinateImage b hb r e hSigns L hL) :=
  ⟨imageFunctional b hb r e hSigns L hL χ,
    imageFunctional_ne_zero b hb r e hSigns L hL χ hχ,
    imageFunctional_invariant b hb r hr e hSigns he L hL χ⟩

theorem kernelImage_diagonal_or_full [FaithfulSMul A Ω]
    (r : X ≃ Fin 4)
    (hr : labelledActionImage (A := A) r = alternatingGroup (Fin 4))
    (e : ∀ x : X, Fin 3 ≃ originalBlockFibre b x)
    (hSigns : coordinateSigns b hb = 1) (he : Coherent b hb e)
    (L : Subgroup A) [L.Normal]
    (hL : L ≤ OriginalBlockClassBound.Kernel (A := A) (X := X))
    (χ : primeRelativeCharacters 3 L) (hχ : χ ≠ 0) :
    coordinateImage b hb r e hSigns
        (OriginalBlockClassBound.Kernel (A := A) (X := X)) le_rfl =
      TernaryA4InvariantSubmodules.diagonal ∨
    coordinateImage b hb r e hSigns
        (OriginalBlockClassBound.Kernel (A := A) (X := X)) le_rfl = ⊤ :=
  TernaryA4InvariantSubmodules.diagonal_or_full_of_retained_head _ _
    (coordinateImage_invariant b hb r hr e hSigns he _ le_rfl)
    (coordinateImage_invariant b hb r hr e hSigns he L hL)
    (coordinateImage_le_kernelImage b hb r e hSigns L hL)
    (coordinateImage_hasInvariantHead b hb r hr e hSigns he L hL χ hχ)

/-- Passing from the literal top range to the original acting group
changes neither its labelled permutations nor its actual image. -/
theorem naturalTop_original_label
    (hTop : IsNaturalA4Action (OriginalBlockClassBound.Top (A := A) (X := X)) X) :
    ∃ r : X ≃ Fin 4, labelledActionImage (A := A) r = alternatingGroup (Fin 4) := by
  obtain ⟨r, hr⟩ := hTop
  refine ⟨r, ?_⟩
  rw [← hr]
  ext g
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨(MulAction.toPermHom A X).rangeRestrict a, rfl⟩
  · rintro ⟨t, rfl⟩
    obtain ⟨a, ha⟩ := t.2
    refine ⟨a, ?_⟩
    change r.permCongr (MulAction.toPermHom A X a) = r.permCongr (t : Equiv.Perm X)
    exact congrArg r.permCongr ha

end DegreeTwelveCoherentTernaryCoordinates

namespace OriginalMinimalBlock

variable {A Ω : Type} [Group A] [MulAction A Ω]
variable [MulAction.IsPretransitive A Ω] {ω₀ : Ω}
variable (D : OriginalMinimalBlock (A := A) ω₀)

/-- The saturated degree-twelve branch supplies coherent charts on its
actual three-point fibres; no new orientation premise remains. -/
theorem degreeTwelve_exists_coherent_ternary_charts
    [Finite A] [Finite Ω] [FaithfulSMul A Ω] [Fintype D.Points]
    [∀ x : D.Points, Fintype (originalBlockFibre D.map x)]
    (N : Subgroup A) [N.Normal]
    (hFibre : Nat.card D.Fibre = 3)
    (hTop : IsNaturalA4Action D.Top D.Points)
    (hOriginalRank : Module.finrank (ZMod 3) (primeRelativeCharacters 3 N) = 2)
    (hTopRank : Module.finrank (ZMod 3)
      (primeRelativeCharacters 3 (originalNormalRange D.topMap N)) = 1) :
    ∃ e : ∀ x : D.Points, Fin 3 ≃ originalBlockFibre D.map x,
      DegreeTwelveCoherentTernaryCoordinates.Coherent D.map D.map_equivariant e := by
  have hSigns := D.ternaryBlock_coordinateSigns_eq_one_of_rank_gt_top N hFibre
    (by rw [hOriginalRank, hTopRank]; decide)
  exact DegreeTwelveCoherentTernaryCoordinates.exists_coherent_charts
    D.map D.map_equivariant D.base (D.ternaryFibreCharts hFibre D.base) hTop hSigns

/-- The saturated 3-by-4 original branch has diagonal or full actual kernel
image in coherent ternary coordinates. The retained head is installed from
the original normal-chain character, not supplied as a coordinate premise. -/
theorem degreeTwelve_kernel_image_diagonal_or_full
    [Finite A] [Finite Ω] [FaithfulSMul A Ω] [Fintype D.Points]
    [∀ x : D.Points, Fintype (originalBlockFibre D.map x)]
    (N : Subgroup A) [N.Normal]
    (hFibre : Nat.card D.Fibre = 3)
    (hTop : IsNaturalA4Action D.Top D.Points)
    (hOriginalRank : Module.finrank (ZMod 3) (primeRelativeCharacters 3 N) = 2)
    (hTopRank : Module.finrank (ZMod 3)
      (primeRelativeCharacters 3 (originalNormalRange D.topMap N)) = 1) :
    ∃ (r : D.Points ≃ Fin 4)
      (e : ∀ x : D.Points, Fin 3 ≃ originalBlockFibre D.map x)
      (hSigns : DegreeThreeBlockInversionHead.coordinateSigns D.map D.map_equivariant = 1),
      labelledActionImage (A := A) r = alternatingGroup (Fin 4) ∧
      DegreeTwelveCoherentTernaryCoordinates.Coherent D.map D.map_equivariant e ∧
      TernaryA4InvariantSubmodules.HasInvariantHead
        (DegreeTwelveCoherentTernaryCoordinates.coordinateImage D.map D.map_equivariant
          r e hSigns (N ⊓ D.topMap.ker) inf_le_right) ∧
      (DegreeTwelveCoherentTernaryCoordinates.coordinateImage D.map D.map_equivariant
          r e hSigns D.topMap.ker le_rfl = TernaryA4InvariantSubmodules.diagonal ∨
        DegreeTwelveCoherentTernaryCoordinates.coordinateImage D.map D.map_equivariant
          r e hSigns D.topMap.ker le_rfl = ⊤) := by
  have hSigns := D.ternaryBlock_coordinateSigns_eq_one_of_rank_gt_top N hFibre
    (by rw [hOriginalRank, hTopRank]; decide)
  obtain ⟨r, hr⟩ := DegreeTwelveCoherentTernaryCoordinates.naturalTop_original_label hTop
  obtain ⟨e, he⟩ := DegreeTwelveCoherentTernaryCoordinates.exists_coherent_charts
    D.map D.map_equivariant D.base (D.ternaryFibreCharts hFibre D.base) hTop hSigns
  obtain ⟨χ, hχ, _hRetained⟩ :=
    D.degreeTwelve_ternaryBlock_exists_retained_character N hOriginalRank hTopRank
  refine ⟨r, e, hSigns, hr, he, ?_, ?_⟩
  · exact DegreeTwelveCoherentTernaryCoordinates.coordinateImage_hasInvariantHead
      D.map D.map_equivariant r hr e hSigns he (N ⊓ D.topMap.ker) inf_le_right χ hχ
  · exact DegreeTwelveCoherentTernaryCoordinates.kernelImage_diagonal_or_full
      D.map D.map_equivariant r hr e hSigns he (N ⊓ D.topMap.ker) inf_le_right χ hχ

end OriginalMinimalBlock
end SymmetricSubgroupAsymptotics

end
