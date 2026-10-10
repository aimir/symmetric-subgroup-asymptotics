import SymmetricSubgroupAsymptotics.CentralBinaryRecursiveCompleteQuotientComparison

/-!
# A universal comparator for two central binary kernel factors

For any finite projective target `A`, the group `(A × C₂) × C₂`
maps onto `A`, `A × C₂`, and itself.  These three maps give a uniform
recursive comparison for any epimorphism onto `A` whose kernel has a
two-step central binary series.  This packages the construction independently
of the particular permutation action used later to realize the comparator.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace DoubleCentralBinaryRecursiveComparison

private abbrev C2 := Multiplicative (ZMod 2)

variable (A : Type*) [Group A] [Finite A]

/-- The universal product comparator for two binary central factors. -/
abbrev Comparator := (A × C2) × C2

/-- Projection onto the projective target. -/
def baseProjection : Comparator A →* A :=
  (MonoidHom.fst A C2).comp (MonoidHom.fst (A × C2) C2)

theorem baseProjection_surjective :
    Function.Surjective (baseProjection A) :=
  Prod.fst_surjective.comp Prod.fst_surjective

/-- Projection onto the target with one binary factor retained. -/
def productProjection : Comparator A →* (A × C2) :=
  MonoidHom.fst (A × C2) C2

theorem productProjection_surjective :
    Function.Surjective (productProjection A) :=
  Prod.fst_surjective

/-- One central binary extension of `A`, controlled by the universal
double-product comparator. -/
noncomputable def centralGlobalComparison
    {R : Type*} [Group R] [Finite R]
    (pi : R →* A)
    (hpi : Function.Surjective pi)
    (hcentral : ∀ z ∈ pi.ker, ∀ x : R, z * x = x * z)
    (hkernel : Nat.card pi.ker ≤ 2) :
    CentralBinaryGlobalComparison (Comparator A) R A where
  projection := pi
  projection_surjective := hpi
  central_kernel := hcentral
  kernel_card_le_two := hkernel
  baseQuotient := baseProjection A
  baseQuotient_surjective := baseProjection_surjective A
  productQuotient := productProjection A
  productQuotient_surjective := productProjection_surjective A

/-- Recursive form of the one-step comparison. -/
noncomputable def centralComparison
    {R : Type*} [Group R] [Finite R]
    (pi : R →* A)
    (hpi : Function.Surjective pi)
    (hcentral : ∀ z ∈ pi.ker, ∀ x : R, z * x = x * z)
    (hkernel : Nat.card pi.ker ≤ 2) :
    CentralBinaryRecursiveComparison (Comparator A) R A :=
  CentralBinaryRecursiveComparison.ofGlobal
    (centralGlobalComparison A pi hpi hcentral hkernel)

/-- The same central extension after adjoining one binary factor.  Its
last required projective product is exactly the universal comparator. -/
noncomputable def centralProductComparison
    {R : Type*} [Group R] [Finite R]
    (pi : R →* A)
    (hpi : Function.Surjective pi)
    (hcentral : ∀ z ∈ pi.ker, ∀ x : R, z * x = x * z)
    (hkernel : Nat.card pi.ker ≤ 2) :
    CentralBinaryRecursiveComparison (Comparator A) (R × C2) (A × C2) := by
  let D := centralComparison A pi hpi hcentral hkernel
  apply D.prodC2 1
  intro b J
  simpa only [Nat.cast_one, one_mul] using
    completeQuotientWeight_le_of_surjective
      (MonoidHom.id (Comparator A)) Function.surjective_id J

/-- Descend the projective map through the selected first central axis. -/
def mapAfterCentralAxis
    {R : Type*} [Group R] [Finite R]
    (pi : R →* A)
    (S : BinaryNormalKernelCentralSeries R pi.ker) :
    R ⧸ S.C →* A :=
  QuotientGroup.lift S.C pi S.C_le_K

theorem mapAfterCentralAxis_surjective
    {R : Type*} [Group R] [Finite R]
    (pi : R →* A)
    (hpi : Function.Surjective pi)
    (S : BinaryNormalKernelCentralSeries R pi.ker) :
    Function.Surjective (mapAfterCentralAxis A pi S) := by
  intro t
  obtain ⟨r, rfl⟩ := hpi t
  exact ⟨QuotientGroup.mk' S.C r, rfl⟩

theorem mapAfterCentralAxis_central_kernel
    {R : Type*} [Group R] [Finite R]
    (pi : R →* A)
    (S : BinaryNormalKernelCentralSeries R pi.ker) :
    ∀ z ∈ (mapAfterCentralAxis A pi S).ker,
      ∀ x, z * x = x * z := by
  intro z hz x
  have hz' : z ∈ pi.ker.map (QuotientGroup.mk' S.C) := by
    simpa only [mapAfterCentralAxis, QuotientGroup.ker_lift] using hz
  exact Subgroup.mem_center_iff.mp (S.quotientKernel_le_center hz') x

theorem mapAfterCentralAxis_kernel_card_le
    {R : Type*} [Group R] [Finite R]
    (pi : R →* A)
    (S : BinaryNormalKernelCentralSeries R pi.ker)
    (hkernel : Nat.card pi.ker ≤ 4) :
    Nat.card (mapAfterCentralAxis A pi S).ker ≤ 2 := by
  let K := pi.ker
  let q : R →* R ⧸ S.C := QuotientGroup.mk' S.C
  let L : Subgroup (R ⧸ S.C) := K.map q
  let f : K →* L := q.subgroupMap K
  have hf : Function.Surjective f := q.subgroupMap_surjective K
  have hker : f.ker = S.C.subgroupOf K := by
    rw [MonoidHom.ker_subgroupMap, QuotientGroup.ker_mk']
  have hkerCard : Nat.card f.ker = 2 := by
    rw [hker,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe S.C_le_K).toEquiv,
      S.C_card]
  have hcard := f.ker.card_mul_index
  rw [Subgroup.index_ker, f.range_eq_top_of_surjective hf,
    Nat.card_congr Subgroup.topEquiv.toEquiv, hkerCard] at hcard
  have hLcard : Nat.card L ≤ 2 := by omega
  have hkerLift : (mapAfterCentralAxis A pi S).ker = L := by
    simpa only [mapAfterCentralAxis, K, q, L,
      QuotientGroup.ker_lift]
  rw [hkerLift]
  exact hLcard

/-- Comparison of the first central quotient with the universal product
comparator. -/
noncomputable def firstCentralComparison
    {R : Type*} [Group R] [Finite R]
    (pi : R →* A)
    (hpi : Function.Surjective pi)
    (S : BinaryNormalKernelCentralSeries R pi.ker)
    (hkernel : Nat.card pi.ker ≤ 4) :
    CentralBinaryRecursiveComparison (Comparator A) (R ⧸ S.C) A :=
  centralComparison A
    (mapAfterCentralAxis A pi S)
    (mapAfterCentralAxis_surjective A pi hpi S)
    (mapAfterCentralAxis_central_kernel A pi S)
    (mapAfterCentralAxis_kernel_card_le A pi S hkernel)

/-- Comparison of the first central quotient times `C₂`. -/
noncomputable def firstCentralProductComparison
    {R : Type*} [Group R] [Finite R]
    (pi : R →* A)
    (hpi : Function.Surjective pi)
    (S : BinaryNormalKernelCentralSeries R pi.ker)
    (hkernel : Nat.card pi.ker ≤ 4) :
    CentralBinaryRecursiveComparison (Comparator A)
      ((R ⧸ S.C) × C2) (A × C2) :=
  centralProductComparison A
    (mapAfterCentralAxis A pi S)
    (mapAfterCentralAxis_surjective A pi hpi S)
    (mapAfterCentralAxis_central_kernel A pi S)
    (mapAfterCentralAxis_kernel_card_le A pi S hkernel)

/-- Full two-step comparison of an arbitrary central-series extension of
`A` with `(A × C₂) × C₂`. -/
noncomputable def centralSeriesComparison
    {R : Type*} [Group R] [Finite R]
    (pi : R →* A)
    (hpi : Function.Surjective pi)
    (S : BinaryNormalKernelCentralSeries R pi.ker)
    (hkernel : Nat.card pi.ker ≤ 4) :
    CentralBinaryRecursiveComparison (Comparator A) R (R ⧸ S.C) := by
  let D := firstCentralComparison A pi hpi S hkernel
  let Dprod := firstCentralProductComparison A pi hpi S hkernel
  refine
    { projection := QuotientGroup.mk' S.C
      projection_surjective := QuotientGroup.mk'_surjective S.C
      central_kernel := ?_
      kernel_card_le_two := ?_
      baseCoefficient := D.coefficient
      productCoefficient := Dprod.coefficient
      base_complete_bound := D.completeQuotientWeight_le
      product_complete_bound := Dprod.completeQuotientWeight_le }
  · intro z hz x
    have hzC : z ∈ S.C := by
      simpa only [QuotientGroup.ker_mk'] using hz
    exact Subgroup.mem_center_iff.mp (S.C_le_center hzC) x
  · rw [QuotientGroup.ker_mk', S.C_card]

/-- Complete all-normal quotient comparison for the two-step extension. -/
theorem centralSeries_completeQuotientWeight_le
    {R : Type*} [Group R] [Finite R]
    (pi : R →* A)
    (hpi : Function.Surjective pi)
    (S : BinaryNormalKernelCentralSeries R pi.ker)
    (hkernel : Nat.card pi.ker ≤ 4)
    {b : ℕ} (J : Subgroup (Equiv.Perm (Fin b))) :
    completeQuotientWeight (R := R) J ≤
      ((centralSeriesComparison A pi hpi S hkernel).coefficient : ℝ) *
        completeQuotientWeight (R := Comparator A) J :=
  (centralSeriesComparison A pi hpi S hkernel).completeQuotientWeight_le J

end DoubleCentralBinaryRecursiveComparison
end SymmetricSubgroupAsymptotics

end
