import SymmetricSubgroupAsymptotics.SubnormalRealCoordinateClassBound
import SymmetricSubgroupAsymptotics.ImprimitiveChiefCoordinates

/-! Class recurrence from subnormal budgets in the ACTUAL stabilizer
components. Every image of the original block kernel is proved NORMAL
in its component by literal equivariant conjugation. The subsequent
normal coordinate-kernel filtration retains all correlations, so budgets
for arbitrary subgroups of the ambient symmetric groups are unnecessary. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical
namespace SymmetricSubgroupAsymptotics.SubnormalPermutationBlockClassReduction
open OriginalBlockClassBound SubnormalRealCoordinateClassBound
variable {A Ω X : Type} [Group A] [MulAction A Ω] [MulAction A X]

def componentCoordinate (b : Ω→X) (hb : ∀(a : A) (ω : Ω),b (a•ω)=a•b ω) (x : X) :
    Kernel (A:=A) (X:=X) →* originalBlockComponent b hb x :=
  originalBlockEvaluation b hb x (Kernel (A:=A) (X:=X)) le_rfl

theorem componentCoordinate_raw (b : Ω→X) (hb : ∀(a : A) (ω : Ω),b (a•ω)=a•b ω)
    (x : X) (k : Kernel (A:=A) (X:=X)) :
    (componentCoordinate b hb x k).val=coordinate b hb x k := rfl

theorem componentCoordinate_range_normal (b : Ω→X)
    (hb : ∀(a : A) (ω : Ω),b (a•ω)=a•b ω) (x : X) :
    (componentCoordinate b hb x).range.Normal := by
  constructor
  rintro _ ⟨k,rfl⟩ g
  obtain ⟨h,rfl⟩ := (originalBlockFibreAction b hb x).rangeRestrict_surjective g
  refine ⟨MulAut.conjNormal (h:A) k,?_⟩
  exact originalBlockEvaluation_conjugation b hb x (Kernel (A:=A) (X:=X)) le_rfl h k

theorem componentCoordinates_injective [FaithfulSMul A Ω] (b : Ω→X)
    (hb : ∀(a : A) (ω : Ω),b (a•ω)=a•b ω) :
    Function.Injective (fun k : Kernel (A:=A) (X:=X)=>fun x=>componentCoordinate b hb x k) := by
  intro k l he
  apply coordinates_injective b hb
  funext x
  exact congrArg (fun z : originalBlockComponent b hb x=>z.val) (congrFun he x)

theorem kernel_class_card_le_subnormal_product [Finite A] [Finite Ω] [Fintype X]
    [FaithfulSMul A Ω] (b : Ω→X) (hb : ∀(a : A) (ω : Ω),b (a•ω)=a•b ω) (c : X→ℕ)
    (hc : ∀x (L : Subgroup (originalBlockComponent b hb x)),
      L.IsSubnormal→Nat.card (ConjClasses L)≤c x) :
    Nat.card (ConjClasses (Kernel (A:=A) (X:=X)))≤∏x,c x :=
  class_card_le_finite_subnormal_coordinate_bounds (fun x=>originalBlockComponent b hb x) c
    (Kernel (A:=A) (X:=X)) (componentCoordinate b hb)
    (fun x=>(componentCoordinate_range_normal b hb x).isSubnormal) hc
    (componentCoordinates_injective b hb)

theorem kernel_real_class_card_le_subnormal_product [Finite A] [Finite Ω] [Fintype X]
    [FaithfulSMul A Ω] (b : Ω→X) (hb : ∀(a : A) (ω : Ω),b (a•ω)=a•b ω)
    (c : X→ℝ) (hc0 : ∀x,0≤c x)
    (hc : ∀x (L : Subgroup (originalBlockComponent b hb x)),
      L.IsSubnormal→(Nat.card (ConjClasses L):ℝ)≤c x) :
    (Nat.card (ConjClasses (Kernel (A:=A) (X:=X))):ℝ)≤∏x,c x :=
  real_class_card_le_finite_subnormal_coordinate_bounds (fun x=>originalBlockComponent b hb x)
    c hc0 (Kernel (A:=A) (X:=X)) (componentCoordinate b hb)
    (fun x=>(componentCoordinate_range_normal b hb x).isSubnormal) hc
    (componentCoordinates_injective b hb)

theorem class_card_le_subnormal_product_mul_top [Finite A] [Finite Ω] [Fintype X]
    [FaithfulSMul A Ω] (b : Ω→X) (hb : ∀(a : A) (ω : Ω),b (a•ω)=a•b ω) (c : X→ℕ)
    (hc : ∀x (L : Subgroup (originalBlockComponent b hb x)),
      L.IsSubnormal→Nat.card (ConjClasses L)≤c x) :
    Nat.card (ConjClasses A)≤(∏x,c x)*Nat.card (ConjClasses (Top (A:=A) (X:=X))) :=
  (conjugacyClass_card_le_kernel_mul_range (topMap (A:=A) (X:=X))).trans
    (Nat.mul_le_mul_right _ (kernel_class_card_le_subnormal_product b hb c hc))

theorem real_class_card_le_subnormal_product_mul_top [Finite A] [Finite Ω] [Fintype X]
    [FaithfulSMul A Ω] (b : Ω→X) (hb : ∀(a : A) (ω : Ω),b (a•ω)=a•b ω)
    (c : X→ℝ) (hc0 : ∀x,0≤c x)
    (hc : ∀x (L : Subgroup (originalBlockComponent b hb x)),
      L.IsSubnormal→(Nat.card (ConjClasses L):ℝ)≤c x) :
    (Nat.card (ConjClasses A):ℝ)≤(∏x,c x)*(Nat.card (ConjClasses (Top (A:=A) (X:=X))):ℝ) := by
  have hs : (Nat.card (ConjClasses A):ℝ)≤
      (Nat.card (ConjClasses (Kernel (A:=A) (X:=X))):ℝ)*
        (Nat.card (ConjClasses (Top (A:=A) (X:=X))):ℝ) := by
    exact_mod_cast conjugacyClass_card_le_kernel_mul_range (topMap (A:=A) (X:=X))
  exact hs.trans (mul_le_mul_of_nonneg_right
    (kernel_real_class_card_le_subnormal_product b hb c hc0 hc) (Nat.cast_nonneg _))

end SymmetricSubgroupAsymptotics.SubnormalPermutationBlockClassReduction
