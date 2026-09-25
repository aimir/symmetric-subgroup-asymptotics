import SymmetricSubgroupAsymptotics.CocycleLifts

/-!
# The shared scalar-top fixture

The order-three top is the actual unit group of the four-element field.
Fixed-top maps are actual homomorphisms of the corresponding semidirect
products. Their classification retains both the linear map and the literal
translation (coboundary) parameter.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace SymmetricSubgroupAsymptotics

section ScalarAction
variable (K V : Type*) [Field K] [AddCommGroup V] [Module K V]

/-- The actual scalar action on the additive group. -/
def scalarUnitAction : Kˣ →* MulAut (Multiplicative V) where
  toFun u :=
    { toFun := fun v ↦ Multiplicative.ofAdd ((u : K) • v.toAdd)
      invFun := fun v ↦ Multiplicative.ofAdd (((u⁻¹ : Kˣ) : K) • v.toAdd)
      left_inv := fun v ↦ by simp [smul_smul]
      right_inv := fun v ↦ by simp [smul_smul]
      map_mul' := fun v w ↦ by exact congrArg Multiplicative.ofAdd (smul_add (u : K) v.toAdd w.toAdd) }
  map_one' := by ext v; simp
  map_mul' u v := by ext w; simp [smul_smul]

abbrev ScalarAffineGroup := (Multiplicative V) ⋊[scalarUnitAction K V] Kˣ

@[simp] theorem scalarAffine_mul_left (x y : ScalarAffineGroup K V) :
    (x*y).left.toAdd = x.left.toAdd + (x.right : K) • y.left.toAdd := rfl

@[simp] theorem scalarAffine_mul_right (x y : ScalarAffineGroup K V) :
    (x*y).right = x.right*y.right := rfl

end ScalarAction

section ScalarMaps
variable {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
  [AddCommGroup W] [Module K W]

abbrev ScalarTopLift := HomomorphicLift
  (SemidirectProduct.rightHom : ScalarAffineGroup K W →* Kˣ)
  (SemidirectProduct.rightHom : ScalarAffineGroup K V →* Kˣ)

@[simp] theorem scalarTopLift_right (f : ScalarTopLift (K := K) (V := V) (W := W))
    (x : ScalarAffineGroup K V) : (f.1 x).right = x.right :=
  homomorphicLift_above _ _ f x

/-- A linear map and translation define an actual fixed-top homomorphism. -/
def scalarAffineLift (L : V →ₗ[K] W) (w : W) : ScalarTopLift (K := K) (V := V) (W := W) :=
  ⟨{ toFun := fun x ↦ ⟨Multiplicative.ofAdd (L x.left.toAdd + w - (x.right : K) • w),x.right⟩
     map_one' := by apply SemidirectProduct.ext <;> simp
     map_mul' := fun x y ↦ by
       apply SemidirectProduct.ext
       · apply Multiplicative.toAdd.injective
         change L (x.left.toAdd + (x.right : K) • y.left.toAdd) + w -
           ((x.right*y.right : Kˣ) : K) • w =
           (L x.left.toAdd+w-(x.right : K) • w) +
             (x.right : K) • (L y.left.toAdd+w-(y.right : K) • w)
         simp only [map_add,map_smul,Units.val_mul,smul_add,smul_sub,mul_smul]
         abel
       · rfl },by apply MonoidHom.ext; intro x; rfl⟩

@[simp] theorem scalarAffineLift_apply_left (L : V →ₗ[K] W) (w : W)
    (x : ScalarAffineGroup K V) :
    ((scalarAffineLift L w).1 x).left.toAdd = L x.left.toAdd+w-(x.right : K) • w := rfl

/-- Restrict an actual fixed-top map to its original additive kernel. -/
def scalarLiftKernelAdd (f : ScalarTopLift (K := K) (V := V) (W := W)) : V →+ W where
  toFun v := (f.1 (SemidirectProduct.inl (Multiplicative.ofAdd v))).left.toAdd
  map_zero' := by simp
  map_add' v w := by
    change (f.1 (SemidirectProduct.inl (Multiplicative.ofAdd (v+w)))).left.toAdd = _
    rw [show (SemidirectProduct.inl (Multiplicative.ofAdd (v+w)) : ScalarAffineGroup K V) =
      SemidirectProduct.inl (Multiplicative.ofAdd v) *
        SemidirectProduct.inl (Multiplicative.ofAdd w) from SemidirectProduct.inl.map_mul _ _]
    rw [f.1.map_mul,scalarAffine_mul_left,scalarTopLift_right]
    simp

private theorem scalarLiftKernelAdd_unit (f : ScalarTopLift (K := K) (V := V) (W := W))
    (u : Kˣ) (v : V) : scalarLiftKernelAdd f ((u : K) • v) =
      (u : K) • scalarLiftKernelAdd f v := by
  have he : (SemidirectProduct.inr u : ScalarAffineGroup K V) *
      SemidirectProduct.inl (Multiplicative.ofAdd v) =
      SemidirectProduct.inl (Multiplicative.ofAdd ((u : K) • v)) * SemidirectProduct.inr u := by
    apply SemidirectProduct.ext
    · change Multiplicative.ofAdd ((0 : V)+(u : K) • v) =
        Multiplicative.ofAdd ((u : K) • v + (1 : K) • (0 : V))
      simp
    · change u*1 = 1*u
      simp
  have h := congrArg (fun x : ScalarAffineGroup K V ↦ (f.1 x).left.toAdd) he
  simp only [map_mul,scalarAffine_mul_left,scalarTopLift_right,SemidirectProduct.right_inl,
    SemidirectProduct.right_inr,Units.val_one,one_smul] at h
  change _ + (u : K) • scalarLiftKernelAdd f v = scalarLiftKernelAdd f ((u : K) • v) + _ at h
  exact (add_left_cancel (h.trans (add_comm _ _))).symm

/-- Equivariance for the full scalar unit group forces genuine field
linearity, including scalar zero. -/
def scalarLiftLinear (f : ScalarTopLift (K := K) (V := V) (W := W)) : V →ₗ[K] W :=
  { scalarLiftKernelAdd f with
    map_smul' := fun a v ↦ by
      by_cases ha : a = 0
      · simp [ha]
      · exact scalarLiftKernelAdd_unit f (Units.mk0 a ha) v }

private theorem scalarLift_decompose (f : ScalarTopLift (K := K) (V := V) (W := W))
    (x : ScalarAffineGroup K V) :
    (f.1 x).left.toAdd = scalarLiftLinear f x.left.toAdd +
      (f.1 (SemidirectProduct.inr x.right)).left.toAdd := by
  have h := congrArg (fun y : ScalarAffineGroup K W ↦ y.left.toAdd)
    (f.1.map_mul (SemidirectProduct.inl x.left) (SemidirectProduct.inr x.right))
  simpa only [SemidirectProduct.inl_left_mul_inr_right,scalarAffine_mul_left,
    scalarTopLift_right,SemidirectProduct.right_inl,Units.val_one,one_smul] using h

private theorem scalarLift_top_commute (f : ScalarTopLift (K := K) (V := V) (W := W))
    (u t : Kˣ) :
    (1-(u : K)) • (f.1 (SemidirectProduct.inr t)).left.toAdd =
      (1-(t : K)) • (f.1 (SemidirectProduct.inr u)).left.toAdd := by
  have he : (SemidirectProduct.inr u : ScalarAffineGroup K V) * SemidirectProduct.inr t =
      SemidirectProduct.inr t * SemidirectProduct.inr u := by rw [← map_mul,← map_mul,mul_comm]
  have h := congrArg (fun x : ScalarAffineGroup K V ↦ (f.1 x).left.toAdd) he
  simp only [map_mul,scalarAffine_mul_left,scalarTopLift_right,SemidirectProduct.right_inr] at h
  simp only [sub_smul,one_smul]
  apply sub_eq_sub_iff_add_eq_add.mpr
  exact h.symm

/-- The retained translation coordinate is recovered from one nonidentity
scalar; no cohomology quotient is taken. -/
def scalarLiftTranslation (u : Kˣ) (f : ScalarTopLift (K := K) (V := V) (W := W)) : W :=
  (1-(u : K))⁻¹ • (f.1 (SemidirectProduct.inr u)).left.toAdd

private theorem scalarLift_top_eq (u : Kˣ) (hu : (u : K) ≠ 1)
    (f : ScalarTopLift (K := K) (V := V) (W := W)) (t : Kˣ) :
    (f.1 (SemidirectProduct.inr t)).left.toAdd =
      scalarLiftTranslation u f - (t : K) • scalarLiftTranslation u f := by
  have hz : (1-(u : K)) ≠ 0 := sub_ne_zero.mpr (Ne.symm hu)
  have h := congrArg (fun w : W ↦ (1-(u : K))⁻¹ • w) (scalarLift_top_commute f u t)
  simp only [smul_smul,inv_mul_cancel₀ hz,one_smul] at h
  rw [h]
  unfold scalarLiftTranslation
  rw [smul_smul,← one_smul K ((1-(u : K))⁻¹ • (f.1 (SemidirectProduct.inr u)).left.toAdd)]
  simp only [smul_smul,one_mul]
  rw [← sub_smul]
  congr 1
  ring

/-- Every actual fixed-top homomorphism has the retained affine formula. -/
theorem scalarTopLift_eq_affine (u : Kˣ) (hu : (u : K) ≠ 1)
    (f : ScalarTopLift (K := K) (V := V) (W := W)) :
    f = scalarAffineLift (scalarLiftLinear f) (scalarLiftTranslation u f) := by
  apply Subtype.ext
  apply MonoidHom.ext
  intro x
  apply SemidirectProduct.ext
  · apply Multiplicative.toAdd.injective
    rw [scalarLift_decompose,scalarLift_top_eq u hu]
    simp only [scalarAffineLift_apply_left]
    abel
  · exact scalarTopLift_right f x

@[simp] theorem scalarLiftLinear_affine (L : V →ₗ[K] W) (w : W) :
    scalarLiftLinear (scalarAffineLift L w) = L := by
  ext v
  simp [scalarLiftLinear,scalarLiftKernelAdd,scalarAffineLift]

@[simp] theorem scalarLiftTranslation_affine (u : Kˣ) (hu : (u : K) ≠ 1)
    (L : V →ₗ[K] W) (w : W) : scalarLiftTranslation u (scalarAffineLift L w) = w := by
  have hz : (1-(u : K)) ≠ 0 := sub_ne_zero.mpr (Ne.symm hu)
  change (1-(u : K))⁻¹ • (L 0+w-(u : K) • w) = w
  rw [map_zero,zero_add]
  have he : w-(u : K) • w = (1-(u : K)) • w := by rw [sub_smul,one_smul]
  rw [he,smul_smul,inv_mul_cancel₀ hz,one_smul]

/-- Exact classification of actual homomorphisms over the same fixed top.
The second coordinate is the retained coboundary, not an H1 class. -/
def scalarTopLiftEquiv (u : Kˣ) (hu : (u : K) ≠ 1) :
    ScalarTopLift (K := K) (V := V) (W := W) ≃ (V →ₗ[K] W) × W where
  toFun f := (scalarLiftLinear f,scalarLiftTranslation u f)
  invFun p := scalarAffineLift p.1 p.2
  left_inv f := (scalarTopLift_eq_affine u hu f).symm
  right_inv p := by simp [scalarLiftTranslation_affine u hu]

/-- Surjectivity is precisely surjectivity of the same linear part; the
retained translation coordinate remains unrestricted. -/
theorem scalarAffineLift_surjective_iff (L : V →ₗ[K] W) (w : W) :
    Function.Surjective (scalarAffineLift L w).1 ↔ Function.Surjective L := by
  constructor
  · intro h y
    obtain ⟨x,hx⟩ := h (SemidirectProduct.inl (Multiplicative.ofAdd y))
    have ht : x.right = 1 := congrArg SemidirectProduct.right hx
    have hl := congrArg (fun z : ScalarAffineGroup K W ↦ z.left.toAdd) hx
    refine ⟨x.left.toAdd,?_⟩
    simpa only [scalarAffineLift_apply_left,ht,Units.val_one,one_smul,
      add_sub_cancel_right,SemidirectProduct.left_inl] using hl
  · intro h y
    obtain ⟨x,hx⟩ := h (y.left.toAdd-w+(y.right : K) • w)
    refine ⟨⟨Multiplicative.ofAdd x,y.right⟩,?_⟩
    apply SemidirectProduct.ext
    · apply Multiplicative.toAdd.injective
      change L x+w-(y.right : K) • w = y.left.toAdd
      rw [hx]
      abel
    · rfl

/-- Onto maps are classified as actual onto linear maps together with every
literal translation parameter. -/
def scalarSurjectiveTopLiftEquiv (u : Kˣ) (hu : (u : K) ≠ 1) :
    {f : ScalarTopLift (K := K) (V := V) (W := W) // Function.Surjective f.1} ≃
      {L : V →ₗ[K] W // Function.Surjective L} × W :=
  ((scalarTopLiftEquiv u hu).subtypeEquiv
    (q := fun p : (V →ₗ[K] W) × W ↦ Function.Surjective p.1)
    (fun f ↦ by
      change Function.Surjective f.1 ↔ Function.Surjective (scalarLiftLinear f)
      conv_lhs => rw [scalarTopLift_eq_affine u hu f]
      exact scalarAffineLift_surjective_iff _ _)).trans
    { toFun := fun p ↦ (⟨p.1.1,p.2⟩,p.1.2)
      invFun := fun p ↦ ⟨(p.1.1,p.2),p.1.2⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }

end ScalarMaps

end SymmetricSubgroupAsymptotics
