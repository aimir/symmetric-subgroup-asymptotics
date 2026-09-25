import SymmetricSubgroupAsymptotics.CanonicalLifts
import SymmetricSubgroupAsymptotics.ComplementCount
import SymmetricSubgroupAsymptotics.SquareLiftFibres

/-!
# Exact lift counts in a central binary extension

The kernel chart identifies an actual elementary abelian kernel with a binary
vector space. The square obstruction retains the span of all squares, not
only the commutators. Subgroups are counted with their literal kernel
intersection before annihilator duality is applied.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics

variable {G K V : Type*} [Group G] [AddCommGroup K] [Module (ZMod 2) K]
  [AddCommGroup V] [Module (ZMod 2) V]

/-- Exponent two is a consequence of the binary scalar structure. -/
theorem binary_mul_pow_two (x : Multiplicative K) : x ^ 2 = 1 := by
  rw [pow_two]
  change x.toAdd + x.toAdd = 0
  rw [← two_smul (ZMod 2), show (2 : ZMod 2) = 0 by decide, zero_smul]

/-- The supplied kernel chart followed by the actual inclusion. -/
def binaryKernelChart (π : G →* Multiplicative V)
    (e : Multiplicative K ≃* π.ker) : Multiplicative K →* G :=
  π.ker.subtype.comp e.toMonoidHom

omit [Module (ZMod 2) K] [Module (ZMod 2) V] in
theorem binaryKernelChart_injective (π : G →* Multiplicative V)
    (e : Multiplicative K ≃* π.ker) : Function.Injective (binaryKernelChart π e) :=
  Subtype.val_injective.comp e.injective

omit [Module (ZMod 2) K] [Module (ZMod 2) V] in
theorem binaryKernelChart_range (π : G →* Multiplicative V)
    (e : Multiplicative K ≃* π.ker) : (binaryKernelChart π e).range = π.ker := by
  ext g
  constructor
  · rintro ⟨k, rfl⟩
    exact (e k).2
  · intro hg
    exact ⟨e.symm ⟨g, hg⟩, by simp [binaryKernelChart]⟩

/-- The ambient subgroup belonging to a literal kernel subspace. -/
def binaryKernelSubgroup (π : G →* Multiplicative V)
    (e : Multiplicative K ≃* π.ker) (W : Submodule (ZMod 2) K) : Subgroup G :=
  W.toAddSubgroup.toSubgroup.map (binaryKernelChart π e)

omit [Module (ZMod 2) V] in
theorem binaryKernelSubgroup_le (π : G →* Multiplicative V)
    (e : Multiplicative K ≃* π.ker) (W : Submodule (ZMod 2) K) :
    binaryKernelSubgroup π e W ≤ π.ker := by
  rw [← binaryKernelChart_range π e]
  intro g hg
  obtain ⟨x, _, rfl⟩ := Subgroup.mem_map.mp hg
  exact ⟨x, rfl⟩

/-- All subgroups of the actual kernel, including their ambient embeddings,
are in bijection with its binary subspaces. -/
def binaryKernelSubmoduleEquiv (π : G →* Multiplicative V)
    (e : Multiplicative K ≃* π.ker) :
    Submodule (ZMod 2) K ≃ {W : Subgroup G // W ≤ π.ker} where
  toFun W := ⟨binaryKernelSubgroup π e W, binaryKernelSubgroup_le π e W⟩
  invFun W := (AddSubgroup.toZModSubmodule 2)
    (AddSubgroup.toSubgroup.symm (W.1.comap (binaryKernelChart π e)))
  left_inv W := by
    change (AddSubgroup.toZModSubmodule 2)
      (AddSubgroup.toSubgroup.symm
        ((W.toAddSubgroup.toSubgroup.map (binaryKernelChart π e)).comap
          (binaryKernelChart π e))) = W
    rw [Subgroup.comap_map_eq_self_of_injective (binaryKernelChart_injective π e)]
    rfl
  right_inv W := by
    apply Subtype.ext
    change (W.1.comap (binaryKernelChart π e)).map (binaryKernelChart π e) = W.1
    rw [Subgroup.map_comap_eq, binaryKernelChart_range, inf_eq_right.mpr W.2]

/-- Every square belongs to the quotient kernel and therefore has a literal
coordinate in the retained kernel chart. -/
def binarySquareCoordinate (π : G →* Multiplicative V)
    (e : Multiplicative K ≃* π.ker) (g : G) : K :=
  (e.symm ⟨g ^ 2, by
    change π (g ^ 2) = 1
    rw [map_pow, binary_mul_pow_two]⟩).toAdd

omit [Module (ZMod 2) K] in
theorem binarySquareCoordinate_chart (π : G →* Multiplicative V)
    (e : Multiplicative K ≃* π.ker) (g : G) :
    binaryKernelChart π e (Multiplicative.ofAdd (binarySquareCoordinate π e g)) =
      g ^ 2 := by
  simp [binaryKernelChart, binarySquareCoordinate]

/-- The exact square obstruction on the current preimage group. For a fixed
image `U`, that group is the preimage of `U`, so this is precisely `Q(U)`. -/
def binarySquareObstruction (π : G →* Multiplicative V)
    (e : Multiplicative K ≃* π.ker) : Submodule (ZMod 2) K :=
  Submodule.span (ZMod 2) (Set.range (binarySquareCoordinate π e))

theorem binarySquareObstruction_le_iff (π : G →* Multiplicative V)
    (e : Multiplicative K ≃* π.ker) (W : Submodule (ZMod 2) K) :
    binarySquareObstruction π e ≤ W ↔
      ∀ g : G, g ^ 2 ∈ binaryKernelSubgroup π e W := by
  rw [binarySquareObstruction, Submodule.span_le, Set.range_subset_iff]
  apply forall_congr'
  intro g
  rw [← binarySquareCoordinate_chart π e g]
  change binarySquareCoordinate π e g ∈ W ↔
    binaryKernelChart π e (Multiplicative.ofAdd (binarySquareCoordinate π e g)) ∈
      W.toAddSubgroup.toSubgroup.map (binaryKernelChart π e)
  exact (Subgroup.mem_map_iff_mem (K := W.toAddSubgroup.toSubgroup)
    (x := Multiplicative.ofAdd (binarySquareCoordinate π e g))
    (binaryKernelChart_injective π e)).symm

section KernelQuotient

variable (π : G →* Multiplicative V) (e : Multiplicative K ≃* π.ker)
  (W : Submodule (ZMod 2) K) [(binaryKernelSubgroup π e W).Normal]
  (hs : ∀ g : G, g ^ 2 ∈ binaryKernelSubgroup π e W)

/-- The kernel chart mapped into the actual square-admissible quotient. -/
def binaryKernelQuotientMap :
    K →ₗ[ZMod 2] SquareQuotientSpace (binaryKernelSubgroup π e W) hs :=
  ((QuotientGroup.mk' (binaryKernelSubgroup π e W)).comp
    (binaryKernelChart π e)).toAdditiveRight.toZModLinearMap 2

omit [Module (ZMod 2) V] in
theorem binaryKernelQuotientMap_ker :
    (binaryKernelQuotientMap π e W hs).ker = W := by
  ext k
  change (QuotientGroup.mk' (binaryKernelSubgroup π e W))
    (binaryKernelChart π e (Multiplicative.ofAdd k)) = 1 ↔ k ∈ W
  exact (QuotientGroup.eq_one_iff _).trans
    (Subgroup.mem_map_iff_mem (K := W.toAddSubgroup.toSubgroup)
      (x := Multiplicative.ofAdd k) (binaryKernelChart_injective π e))

omit [Module (ZMod 2) V] in
theorem binaryKernelQuotientMap_range :
    (binaryKernelQuotientMap π e W hs).range =
      squareKernelSubmodule (binaryKernelSubgroup π e W) hs π := by
  ext x
  change (∃ k : K, Additive.ofMul ((QuotientGroup.mk' (binaryKernelSubgroup π e W))
      (binaryKernelChart π e (Multiplicative.ofAdd k))) = x) ↔
    Additive.toMul x ∈ π.ker.map (QuotientGroup.mk' (binaryKernelSubgroup π e W))
  constructor
  · rintro ⟨k, rfl⟩
    exact Subgroup.mem_map.mpr ⟨binaryKernelChart π e (Multiplicative.ofAdd k),
      (e (Multiplicative.ofAdd k)).2, rfl⟩
  · rintro ⟨g, hg, hx⟩
    refine ⟨(e.symm ⟨g, hg⟩).toAdd, ?_⟩
    change Additive.ofMul ((QuotientGroup.mk' (binaryKernelSubgroup π e W))
      (binaryKernelChart π e (e.symm ⟨g, hg⟩))) = x
    have he : binaryKernelChart π e (e.symm ⟨g, hg⟩) = g := by
      change (e (e.symm ⟨g, hg⟩)).val = g
      simp
    rw [he, hx]
    rfl

/-- The retained linear kernel is exactly `K/W`, by an actual equivalence. -/
def binaryKernelQuotientEquiv :
    (K ⧸ W) ≃ₗ[ZMod 2] squareKernelSubmodule (binaryKernelSubgroup π e W) hs π :=
  (Submodule.quotEquivOfEq _ _ (binaryKernelQuotientMap_ker π e W hs).symm).trans
    ((binaryKernelQuotientMap π e W hs).quotKerEquivRange.trans
      (LinearEquiv.ofEq _ _ (binaryKernelQuotientMap_range π e W hs)))

include hs in
/-- Every admissible fixed-intersection fibre has the full original
kernel-codimension weight. -/
theorem binary_lift_fibre_card [Finite G] (hπ : Function.Surjective π) :
    Nat.card (SquareLiftFibre π (binaryKernelSubgroup π e W)) =
      2 ^ (Module.finrank (ZMod 2) V * Module.finrank (ZMod 2) (K ⧸ W)) := by
  rw [squareLiftFibre_card (binaryKernelSubgroup π e W) hs π hπ
    (binaryKernelSubgroup_le π e W), ← (binaryKernelQuotientEquiv π e W hs).finrank_eq]

end KernelQuotient

omit [Module (ZMod 2) V] in
theorem binaryKernelChart_pow_two (π : G →* Multiplicative V)
    (e : Multiplicative K ≃* π.ker) (g : G) (hg : g ∈ π.ker) : g ^ 2 = 1 := by
  have he : binaryKernelChart π e (e.symm ⟨g, hg⟩) = g := by
    change (e (e.symm ⟨g, hg⟩)).val = g
    simp
  rw [← he, ← map_pow, binary_mul_pow_two, map_one]

/-- Partition the actual full-image subgroups by their actual kernel
intersection. Only square-admissible intersections occur. -/
def binaryAllLiftFibreEquiv (π : G →* Multiplicative V)
    (e : Multiplicative K ≃* π.ker) (hcentral : π.ker ≤ Subgroup.center G) :
    (Σ W : {W : Submodule (ZMod 2) K // binarySquareObstruction π e ≤ W},
      SquareLiftFibre π (binaryKernelSubgroup π e W.1)) ≃
    {H : Subgroup G // H.map π = ⊤} := by
  let f : (Σ W : {W : Submodule (ZMod 2) K // binarySquareObstruction π e ≤ W},
      SquareLiftFibre π (binaryKernelSubgroup π e W.1)) →
      {H : Subgroup G // H.map π = ⊤} := fun X ↦ ⟨X.2.1, X.2.2.1⟩
  refine Equiv.ofBijective f ⟨?_, ?_⟩
  · rintro ⟨W, H⟩ ⟨W', H'⟩ h
    have hH : H.1 = H'.1 := congrArg Subtype.val h
    have hw : W = W' := by
      apply Subtype.ext
      apply (binaryKernelSubmoduleEquiv π e).injective
      apply Subtype.ext
      change binaryKernelSubgroup π e W.1 = binaryKernelSubgroup π e W'.1
      rw [← H.2.2, ← H'.2.2, hH]
    subst W'
    have hh : H = H' := Subtype.ext hH
    subst H'
    rfl
  · intro H
    let W := (binaryKernelSubmoduleEquiv π e).symm ⟨H.1 ⊓ π.ker, inf_le_right⟩
    have hW : binaryKernelSubgroup π e W = H.1 ⊓ π.ker :=
      congrArg Subtype.val ((binaryKernelSubmoduleEquiv π e).apply_symm_apply
        ⟨H.1 ⊓ π.ker, inf_le_right⟩)
    have hs : binarySquareObstruction π e ≤ W := by
      apply (binarySquareObstruction_le_iff π e W).mpr
      exact squares_mem_of_lift π hcentral (binaryKernelChart_pow_two π e)
        binary_mul_pow_two _ H.1 H.2 hW.symm
    exact ⟨⟨⟨W, hs⟩, ⟨H.1, H.2, hW.symm⟩⟩, rfl⟩

section FiniteCount

variable [Finite G] [Finite K]

attribute [local instance] Fintype.ofFinite

private instance : Finite (Module.Dual (ZMod 2) K) :=
  Finite.of_injective (fun f : Module.Dual (ZMod 2) K ↦ (f : K → ZMod 2))
    DFunLike.coe_injective

/-- The all-lifts count before annihilator reindexing. The square condition
is imposed on the actual kernel intersection, and each fibre is proved. -/
theorem binary_all_lifts_count (π : G →* Multiplicative V)
    (hπ : Function.Surjective π) (e : Multiplicative K ≃* π.ker)
    (hcentral : π.ker ≤ Subgroup.center G) :
    Nat.card {H : Subgroup G // H.map π = ⊤} =
      ∑ W : {W : Submodule (ZMod 2) K // binarySquareObstruction π e ≤ W},
        2 ^ (Module.finrank (ZMod 2) V * Module.finrank (ZMod 2) (K ⧸ W.1)) := by
  letI (W : {W : Submodule (ZMod 2) K // binarySquareObstruction π e ≤ W}) :
      Finite (SquareLiftFibre π (binaryKernelSubgroup π e W.1)) :=
    inferInstanceAs (Finite {H : Subgroup G //
      H.map π = ⊤ ∧ H ⊓ π.ker = binaryKernelSubgroup π e W.1})
  rw [← Nat.card_congr (binaryAllLiftFibreEquiv π e hcentral), Nat.card_sigma]
  apply Finset.sum_congr rfl
  intro W _
  letI := normal_of_le_central_kernel π hcentral (binaryKernelSubgroup π e W.1)
    (binaryKernelSubgroup_le π e W.1)
  exact binary_lift_fibre_card π e W.1
    ((binarySquareObstruction_le_iff π e W.1).mp W.2) hπ

/-- The exact annihilator-aware all-lifts identity for a central binary
extension. The canonical lift is the zero-annihilator summand. -/
theorem binary_all_lifts_count_annihilator (π : G →* Multiplicative V)
    (hπ : Function.Surjective π) (e : Multiplicative K ≃* π.ker)
    (hcentral : π.ker ≤ Subgroup.center G) :
    Nat.card {H : Subgroup G // H.map π = ⊤} =
      ∑ B : Submodule (ZMod 2) (binarySquareObstruction π e).dualAnnihilator,
        2 ^ (Module.finrank (ZMod 2) V * Module.finrank (ZMod 2) B) := by
  rw [binary_all_lifts_count π hπ e hcentral, retainedAnnihilator_weight_sum]

/-- The same actual subgroup count in the explicit Gaussian-polynomial
form used in the manuscript. -/
theorem binary_all_lifts_count_gaussian (π : G →* Multiplicative V)
    (hπ : Function.Surjective π) (e : Multiplicative K ≃* π.ker)
    (hcentral : π.ker ≤ Subgroup.center G) :
    (Nat.card {H : Subgroup G // H.map π = ⊤} : ℚ) =
      ∑ j ∈ Finset.range
        (Module.finrank (ZMod 2) (binarySquareObstruction π e).dualAnnihilator + 1),
        binaryGaussianCoefficient
          (Module.finrank (ZMod 2) (binarySquareObstruction π e).dualAnnihilator) j *
          2 ^ (Module.finrank (ZMod 2) V * j) := by
  rw [binary_all_lifts_count_annihilator π hπ e hcentral, Nat.cast_sum]
  simp only [Nat.cast_pow, Nat.cast_ofNat]
  exact binary_subspace_weight_sum _

end FiniteCount

/-- The subgroup belonging to a binary subspace has that subspace as its
literal additive group. -/
def binarySubspaceGroupEquiv (U : Submodule (ZMod 2) V) :
    U.toAddSubgroup.toSubgroup ≃* Multiplicative U where
  toFun x := Multiplicative.ofAdd ⟨x.1.toAdd, x.2⟩
  invFun x := ⟨Multiplicative.ofAdd x.toAdd.1, x.toAdd.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

/-- Restrict to the preimage of `U` while retaining `U` as a binary target. -/
def binaryRestrictedProjection (π : G →* Multiplicative V)
    (U : Submodule (ZMod 2) V) :
    U.toAddSubgroup.toSubgroup.comap π →* Multiplicative U :=
  (binarySubspaceGroupEquiv U).toMonoidHom.comp
    (π.subgroupComap U.toAddSubgroup.toSubgroup)

theorem binaryRestrictedProjection_surjective (π : G →* Multiplicative V)
    (hπ : Function.Surjective π) (U : Submodule (ZMod 2) V) :
    Function.Surjective (binaryRestrictedProjection π U) :=
  (binarySubspaceGroupEquiv U).surjective.comp
    (π.subgroupComap_surjective_of_surjective U.toAddSubgroup.toSubgroup hπ)

theorem binaryRestrictedProjection_ker (π : G →* Multiplicative V)
    (U : Submodule (ZMod 2) V) :
    (binaryRestrictedProjection π U).ker =
      (π.subgroupComap U.toAddSubgroup.toSubgroup).ker := by
  ext g
  change Multiplicative.ofAdd (⟨(π g.1).toAdd, g.2⟩ : U) = 1 ↔
    (⟨π g.1, g.2⟩ : U.toAddSubgroup.toSubgroup) = 1
  change (⟨(π g.1).toAdd, g.2⟩ : U) = 0 ↔
    (⟨π g.1, g.2⟩ : U.toAddSubgroup.toSubgroup) = 1
  rw [Subtype.ext_iff, Subtype.ext_iff]
  rfl

/-- Transporting the original kernel chart to a preimage does not change
the kernel coordinate space. -/
def binaryRestrictedKernelChart (π : G →* Multiplicative V)
    (e : Multiplicative K ≃* π.ker) (U : Submodule (ZMod 2) V) :
    Multiplicative K ≃* (binaryRestrictedProjection π U).ker :=
  (e.trans (restrictedKernelEquiv π U.toAddSubgroup.toSubgroup).symm).trans
    (MulEquiv.subgroupCongr (binaryRestrictedProjection_ker π U).symm)

/-- The true ambient fixed-image fibre is the full-image fibre of the
restricted binary projection. -/
def binaryImageLiftEquiv (π : G →* Multiplicative V)
    (U : Submodule (ZMod 2) V) :
    {H : Subgroup G // H.map π = U.toAddSubgroup.toSubgroup} ≃
      {L : Subgroup (U.toAddSubgroup.toSubgroup.comap π) //
        L.map (binaryRestrictedProjection π U) = ⊤} :=
  (imageLiftEquiv π U.toAddSubgroup.toSubgroup).trans
    (Equiv.subtypeEquivRight fun L ↦ by
      rw [binaryRestrictedProjection, ← Subgroup.map_map,
        ← Subgroup.map_top_of_surjective (binarySubspaceGroupEquiv U).toMonoidHom
          (binarySubspaceGroupEquiv U).surjective]
      exact (Subgroup.map_injective (binarySubspaceGroupEquiv U).injective).eq_iff.symm)

theorem binaryRestrictedProjection_central (π : G →* Multiplicative V)
    (hcentral : π.ker ≤ Subgroup.center G) (U : Submodule (ZMod 2) V) :
    (binaryRestrictedProjection π U).ker ≤
      Subgroup.center (U.toAddSubgroup.toSubgroup.comap π) := by
  rw [binaryRestrictedProjection_ker]
  intro k hk
  rw [Subgroup.mem_center_iff]
  intro g
  apply Subtype.ext
  exact Subgroup.mem_center_iff.mp (hcentral (congrArg Subtype.val hk)) g.1

/-- The square obstruction for the specified image, in the original kernel
coordinate space. -/
def binaryImageSquareObstruction (π : G →* Multiplicative V)
    (e : Multiplicative K ≃* π.ker) (U : Submodule (ZMod 2) V) : Submodule (ZMod 2) K :=
  binarySquareObstruction (binaryRestrictedProjection π U) (binaryRestrictedKernelChart π e U)

omit [Module (ZMod 2) K] in
/-- Restriction preserves every original square coordinate. -/
theorem binarySquareCoordinate_restricted (π : G →* Multiplicative V)
    (e : Multiplicative K ≃* π.ker) (U : Submodule (ZMod 2) V)
    (g : U.toAddSubgroup.toSubgroup.comap π) :
    binarySquareCoordinate (binaryRestrictedProjection π U)
      (binaryRestrictedKernelChart π e U) g = binarySquareCoordinate π e g.1 := rfl

/-- The retained condition is exactly the span of squares above `U`, tested
in the original kernel coordinates. -/
theorem binaryImageSquareObstruction_le_iff (π : G →* Multiplicative V)
    (e : Multiplicative K ≃* π.ker) (U : Submodule (ZMod 2) V)
    (W : Submodule (ZMod 2) K) :
    binaryImageSquareObstruction π e U ≤ W ↔
      ∀ g : G, (π g).toAdd ∈ U → binarySquareCoordinate π e g ∈ W := by
  rw [binaryImageSquareObstruction, binarySquareObstruction, Submodule.span_le,
    Set.range_subset_iff]
  simp only [binarySquareCoordinate_restricted]
  constructor
  · intro h g hg
    exact h ⟨g, hg⟩
  · intro h g
    exact h g.1 g.2

section ImageCount

variable [Finite G] [Finite K]

attribute [local instance] Fintype.ofFinite

private instance : Finite (Module.Dual (ZMod 2) K) :=
  Finite.of_injective (fun f : Module.Dual (ZMod 2) K ↦ (f : K → ZMod 2))
    DFunLike.coe_injective

/-- Exact all-lifts formula for every specified binary image `U`, counting
literal ambient subgroups and retaining the original square annihilator. -/
theorem binary_image_lifts_count_annihilator (π : G →* Multiplicative V)
    (hπ : Function.Surjective π) (e : Multiplicative K ≃* π.ker)
    (hcentral : π.ker ≤ Subgroup.center G) (U : Submodule (ZMod 2) V) :
    Nat.card {H : Subgroup G // H.map π = U.toAddSubgroup.toSubgroup} =
      ∑ B : Submodule (ZMod 2) (binaryImageSquareObstruction π e U).dualAnnihilator,
        2 ^ (Module.finrank (ZMod 2) U * Module.finrank (ZMod 2) B) := by
  rw [Nat.card_congr (binaryImageLiftEquiv π U)]
  exact binary_all_lifts_count_annihilator (binaryRestrictedProjection π U)
    (binaryRestrictedProjection_surjective π hπ U) (binaryRestrictedKernelChart π e U)
    (binaryRestrictedProjection_central π hcentral U)

/-- The full fixed-image count in closed Gaussian-polynomial form. -/
theorem binary_image_lifts_count_gaussian (π : G →* Multiplicative V)
    (hπ : Function.Surjective π) (e : Multiplicative K ≃* π.ker)
    (hcentral : π.ker ≤ Subgroup.center G) (U : Submodule (ZMod 2) V) :
    (Nat.card {H : Subgroup G // H.map π = U.toAddSubgroup.toSubgroup} : ℚ) =
      ∑ j ∈ Finset.range
        (Module.finrank (ZMod 2) (binaryImageSquareObstruction π e U).dualAnnihilator + 1),
        binaryGaussianCoefficient
          (Module.finrank (ZMod 2) (binaryImageSquareObstruction π e U).dualAnnihilator) j *
          2 ^ (Module.finrank (ZMod 2) U * j) := by
  rw [Nat.card_congr (binaryImageLiftEquiv π U)]
  exact binary_all_lifts_count_gaussian (binaryRestrictedProjection π U)
    (binaryRestrictedProjection_surjective π hπ U) (binaryRestrictedKernelChart π e U)
    (binaryRestrictedProjection_central π hcentral U)

end ImageCount

end SymmetricSubgroupAsymptotics
