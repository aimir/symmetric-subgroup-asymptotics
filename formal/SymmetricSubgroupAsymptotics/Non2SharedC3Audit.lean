import SymmetricSubgroupAsymptotics.Non2LiftBound
import SymmetricSubgroupAsymptotics.SharedC3Counts

/-!
# The shared-C3 audit for the numerical cocycle bound

The scalar representation and kernel chart are actual actions and maps.
The first cohomology is trivial, but the full coboundary space has size
4^m; that factor must remain in a homomorphism count.
-/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics

open groupCohomology

universe u
variable (K V : Type u) [Field K] [AddCommGroup V] [Module K V]

/-- The original scalar action of the full unit group. -/
abbrev scalarUnitRep : Rep K Kˣ := Rep.of
  { toFun := fun t ↦ (t : K) • (LinearMap.id : V →ₗ[K] V)
    map_one' := by ext v; simp
    map_mul' := fun s t ↦ by ext v; simp [smul_smul, mul_comm] }

/-- The scalar semidirect product has its literal additive group as
kernel, with precisely the scalar quotient action. -/
def scalarOriginalKernelChart : OriginalKernelModuleChart
    (SemidirectProduct.rightHom : ScalarAffineGroup K V →* Kˣ) (scalarUnitRep K V) where
  equiv :=
    { toFun := fun a ↦ ⟨SemidirectProduct.inl a, by simp [MonoidHom.mem_ker]⟩
      invFun := fun x ↦ x.1.left
      left_inv := fun _ ↦ rfl
      right_inv := fun x ↦ by
        apply Subtype.ext
        apply SemidirectProduct.ext
        · rfl
        · exact x.property.symm
      map_mul' := fun a b ↦ Subtype.ext (SemidirectProduct.inl.map_mul a b) }
  conjugate q a := by
    apply SemidirectProduct.ext
    · apply Multiplicative.toAdd.injective
      change (q.right : K) • a =
        q.left.toAdd + (q.right : K) • a +
          ((q.right * 1 : Kˣ) : K) • (((q.right⁻¹ : Kˣ) : K) • (-q.left.toAdd))
      simp [smul_smul]
    · simp

variable {K V}

/-- Evaluation at a nonidentity scalar is injective on coboundaries.
Consequently all translations remain distinct actual cocycles. -/
theorem scalarCoboundary_injective (u : Kˣ) (hu : (u : K) ≠ 1) :
    Function.Injective (d₀₁ (scalarUnitRep K V)) := by
  intro a b h
  have he := congrFun h u
  change (u : K) • a - a = (u : K) • b - b at he
  have he' : ((u : K)-1) • a = ((u : K)-1) • b := by
    simpa only [sub_smul, one_smul] using he
  exact (smul_right_injective V (sub_ne_zero.mpr hu)) he'

/-- Every scalar-top cocycle is an actual coboundary, with no quotient
by the translation parameter in the cocycle space. -/
theorem scalarCocycle_is_coboundary (u : Kˣ) (hu : (u : K) ≠ 1)
    (z : cocycles₁ (scalarUnitRep K V)) : (z : Kˣ → V) ∈
      coboundaries₁ (scalarUnitRep K V) := by
  let a : V := ((u : K)-1)⁻¹ • z u
  refine ⟨a, ?_⟩
  funext t
  change (t : K) • a - a = z t
  have h₁ : z (u*t) = (u : K) • z t + z u :=
    (mem_cocycles₁_iff _).mp z.2 u t
  have h₂ : z (t*u) = (t : K) • z u + z t :=
    (mem_cocycles₁_iff _).mp z.2 t u
  have he : ((u : K)-1) • z t = ((t : K)-1) • z u := by
    simp only [sub_smul, one_smul]
    apply sub_eq_sub_iff_add_eq_add.mpr
    exact h₁.symm.trans ((congrArg z (mul_comm u t)).trans h₂)
  calc
    (t : K) • a - a = ((t : K)-1) • a := by simp [sub_smul]
    _ = ((u : K)-1)⁻¹ • (((t : K)-1) • z u) := by
      simp only [a, smul_smul, mul_comm]
    _ = ((u : K)-1)⁻¹ • (((u : K)-1) • z t) := by rw [he]
    _ = z t := by rw [smul_smul, inv_mul_cancel₀ (sub_ne_zero.mpr hu), one_smul]

theorem scalarH1_subsingleton (u : Kˣ) (hu : (u : K) ≠ 1) :
    Subsingleton (H1 (scalarUnitRep K V)) := by
  apply subsingleton_of_forall_eq 0
  intro x
  refine H1_induction_on x (fun z ↦ ?_)
  exact (H1π_eq_zero_iff z).mpr (scalarCocycle_is_coboundary u hu z)

theorem scalarH1_card (u : Kˣ) (hu : (u : K) ≠ 1) :
    Nat.card (H1 (scalarUnitRep K V)) = 1 := by
  letI := scalarH1_subsingleton (V := V) u hu
  exact Nat.card_eq_one_iff_unique.mpr ⟨inferInstance, inferInstance⟩

theorem scalarCoboundaries_card (u : Kˣ) (hu : (u : K) ≠ 1) :
    Nat.card (coboundaries₁ (scalarUnitRep K V)) = Nat.card V := by
  exact Nat.card_congr (Equiv.ofBijective
    (fun a : V ↦ (⟨d₀₁ (scalarUnitRep K V) a, ⟨a, rfl⟩⟩ :
      coboundaries₁ (scalarUnitRep K V)))
    ⟨fun a b h ↦ scalarCoboundary_injective u hu (congrArg Subtype.val h),
      by rintro ⟨z, a, ha⟩; exact ⟨a, Subtype.ext ha⟩⟩).symm

private theorem sharedC3_audit_unit : ∃ u : SharedF4ˣ, (u : SharedF4) ≠ 1 := by
  haveI : Nontrivial SharedF4ˣ := Finite.one_lt_card_iff_nontrivial.mp
    (by rw [sharedC3_top_card]; norm_num)
  obtain ⟨u, hu⟩ := exists_ne (1 : SharedF4ˣ)
  exact ⟨u, fun h ↦ hu (Units.ext h)⟩

/-- The mandatory c=1 fixture uses the actual scalar target module. -/
abbrev SharedC3Module (m : ℕ) := scalarUnitRep SharedF4 (Fin m → SharedF4)

theorem sharedC3_H1_card (m : ℕ) : Nat.card (H1 (SharedC3Module m)) = 1 := by
  obtain ⟨u, hu⟩ := sharedC3_audit_unit
  exact scalarH1_card u hu

theorem sharedC3_coboundaries_card (m : ℕ) :
    Nat.card (coboundaries₁ (SharedC3Module m)) = 4^m := by
  obtain ⟨u, hu⟩ := sharedC3_audit_unit
  rw [scalarCoboundaries_card u hu]
  simp [Nat.card_fun, sharedF4_card]

/-- These are cocycles on one actual F4^r semidirect C3, not separately
chosen sources for different target columns. -/
theorem sharedC3_pulledback_cocycles_card (r m : ℕ) :
    Nat.card (cocycles₁ (quotientPullbackRep
      (SemidirectProduct.rightHom : SharedC3Group r →* SharedF4ˣ)
      (SharedC3Module m))) = 4^(m*(r+1)) := by
  let f₀ : SharedC3FixedTopHom r m := scalarAffineLift 0 0
  rw [← Nat.card_congr (homomorphicLiftModuleCocycleEquiv _ _
    (SharedC3Module m) (scalarOriginalKernelChart SharedF4 (Fin m → SharedF4)) f₀)]
  exact sharedC3_fixedTopHom_card r m

/-- The exact restriction image has full expected F4-linear capacity.
Its size is derived from actual lifts and actual cohomology, rather than
postulated as an independent column count. -/
theorem sharedC3_restriction_image_card (r m : ℕ) :
    Nat.card (LinearMap.range (quotientCocycleRestriction
      (SemidirectProduct.rightHom : SharedC3Group r →* SharedF4ˣ)
      (SharedC3Module m))) = 4^(m*r) := by
  have h := cocycles_card_eq_quotient_mul_restriction_range
    (SemidirectProduct.rightHom : SharedC3Group r →* SharedF4ˣ)
    SemidirectProduct.rightHom_surjective (SharedC3Module m)
  rw [sharedC3_pulledback_cocycles_card,
    cocycles_card_eq_coboundaries_mul_H1, sharedC3_coboundaries_card,
    sharedC3_H1_card, mul_one] at h
  have hp : (4 : ℕ)^(m*(r+1)) = 4^m * 4^(m*r) := by
    rw [← pow_add]
    congr 1
    ring
  exact Nat.eq_of_mul_eq_mul_left (by positivity : 0 < (4 : ℕ)^m)
    (h.symm.trans hp)

/-- The two cocycle marks retain one shared source and both full
translation factors. This audits the joint-source moment interface. -/
theorem sharedC3_two_cocycle_marks_card (r m₁ m₂ : ℕ) :
    Nat.card
      (cocycles₁ (quotientPullbackRep
        (SemidirectProduct.rightHom : SharedC3Group r →* SharedF4ˣ) (SharedC3Module m₁)) ×
       cocycles₁ (quotientPullbackRep
        (SemidirectProduct.rightHom : SharedC3Group r →* SharedF4ˣ) (SharedC3Module m₂))) =
      4^((m₁+m₂)*(r+1)) := by
  rw [Nat.card_prod, sharedC3_pulledback_cocycles_card,
    sharedC3_pulledback_cocycles_card, ← pow_add]
  congr 1
  ring

end SymmetricSubgroupAsymptotics
