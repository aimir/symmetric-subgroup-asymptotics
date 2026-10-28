import SymmetricSubgroupAsymptotics.CFSGAdditiveRootExtraction
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDGenerationPrimitiveRootSaturation

/-! A genuine two-root filter: one torus fixes the first commuting root
and scales the second. Its commuting Weyl conjugate may act differently
on the first root, but the actual double commutator eliminates that
coordinate exactly and retains the product of two potentially different scalar differences.
This permits genuine Coxeter-conjugate torus weights rather than requiring
the same second-root eigenvalue twice. -/
set_option autoImplicit false
noncomputable section
open scoped commutatorElement
namespace SymmetricSubgroupAsymptotics.CFSGUnequalTwoRootExtraction
variable {K G : Type*} [Field K] [Group G]

def pairScale (a b : K) : K × K →+ K × K where
  toFun v := (a * v.1, b * v.2)
  map_zero' := by ext <;> exact mul_zero _
  map_add' v w := by ext <;> simp only [Prod.fst_add, Prod.snd_add, mul_add]

theorem two_root_double_commutator (A B : K → G)
    (hA : ∀ a b : K, A (a + b) = A a * A b) (hA0 : A 0 = 1)
    (hB : ∀ a b : K, B (a + b) = B a * B b) (hB0 : B 0 = 1)
    (hAB : ∀ a b : K, Commute (A a) (B b))
    (h w : G) (k l m : K)
    (hScaleA : ∀ a, h * A a * h⁻¹ = A a)
    (hScaleB : ∀ b, h * B b * h⁻¹ = B (k * b))
    (hScaleA' : ∀ a, (w * h * w⁻¹) * A a * (w * h * w⁻¹)⁻¹ = A (l * a))
    (hScaleB' : ∀ b, (w * h * w⁻¹) * B b * (w * h * w⁻¹)⁻¹ = B (m * b))
    (hComm : Commute (w * h * w⁻¹) h) :
    ⁅(A 1 * B 1 * w) * h * (A 1 * B 1 * w)⁻¹, h⁆ = B ((1 - k) * (1 - m)) := by
  let root : K × K → G := fun v => A v.1 * B v.2
  have hAdd : ∀ v z : K × K, root (v + z) = root v * root z := by
    intro v z
    change A (v.1 + z.1) * B (v.2 + z.2) = (A v.1 * B v.2) * (A z.1 * B z.2)
    rw [hA, hB]
    calc
      (A v.1 * A z.1) * (B v.2 * B z.2) = A v.1 * (A z.1 * B v.2) * B z.2 := by group
      _ = A v.1 * (B v.2 * A z.1) * B z.2 := by rw [(hAB z.1 v.2).eq]
      _ = (A v.1 * B v.2) * (A z.1 * B z.2) := by group
  have hZero : root 0 = 1 := by change A 0 * B 0 = 1; rw [hA0, hB0, one_mul]
  have hs : ∀ v, h * root v * h⁻¹ = root (pairScale (1 : K) k v) := by
    intro v
    change h * (A v.1 * B v.2) * h⁻¹ = A (1 * v.1) * B (k * v.2)
    calc
      h * (A v.1 * B v.2) * h⁻¹ = (h * A v.1 * h⁻¹) * (h * B v.2 * h⁻¹) := by group
      _ = A (1 * v.1) * B (k * v.2) := by rw [hScaleA, hScaleB, one_mul]
  have hs' : ∀ v, (w * h * w⁻¹) * root v * (w * h * w⁻¹)⁻¹ = root (pairScale l m v) := by
    intro v
    change (w * h * w⁻¹) * (A v.1 * B v.2) * (w * h * w⁻¹)⁻¹ = A (l * v.1) * B (m * v.2)
    calc
      (w * h * w⁻¹) * (A v.1 * B v.2) * (w * h * w⁻¹)⁻¹ =
          ((w * h * w⁻¹) * A v.1 * (w * h * w⁻¹)⁻¹) *
          ((w * h * w⁻¹) * B v.2 * (w * h * w⁻¹)⁻¹) := by group
      _ = A (l * v.1) * B (m * v.2) := by rw [hScaleA', hScaleB']
  have he : ((1, 1) : K × K) - pairScale l m (1, 1) -
      pairScale 1 k ((1, 1) - pairScale l m (1, 1)) = (0, (1 - k) * (1 - m)) := by
    ext
    · change (1 : K) - l * 1 - 1 * (1 - l * 1) = 0
      ring
    · change (1 : K) - m * 1 - k * (1 - m * 1) = (1 - k) * (1 - m)
      ring
  have h := CFSGAdditiveRootExtraction.double_commutator root hAdd hZero h w
    (pairScale 1 k) (pairScale l m) (1, 1) hs hs' hComm
  rw [he] at h
  simpa only [root, hA0, one_mul] using h

theorem pure_second_root_mem (A B : K → G)
    (hA : ∀ a b : K, A (a + b) = A a * A b) (hA0 : A 0 = 1)
    (hB : ∀ a b : K, B (a + b) = B a * B b) (hB0 : B 0 = 1)
    (hAB : ∀ a b : K, Commute (A a) (B b))
    (h w : G) (k l m : K)
    (hScaleA : ∀ a, h * A a * h⁻¹ = A a)
    (hScaleB : ∀ b, h * B b * h⁻¹ = B (k * b))
    (hScaleA' : ∀ a, (w * h * w⁻¹) * A a * (w * h * w⁻¹)⁻¹ = A (l * a))
    (hScaleB' : ∀ b, (w * h * w⁻¹) * B b * (w * h * w⁻¹)⁻¹ = B (m * b))
    (hComm : Commute (w * h * w⁻¹) h)
    (H : Subgroup G) (hh : h ∈ H) (hy : A 1 * B 1 * w ∈ H) : B ((1 - k) * (1 - m)) ∈ H := by
  rw [← two_root_double_commutator A B hA hA0 hB hB0 hAB h w k l m
    hScaleA hScaleB hScaleA' hScaleB' hComm, commutatorElement_def]
  have hx := H.mul_mem (H.mul_mem hy hh) (H.inv_mem hy)
  exact H.mul_mem (H.mul_mem (H.mul_mem hx hh) (H.inv_mem hx)) (H.inv_mem hh)

theorem all_second_parameters [Finite K] (A B : K → G)
    (hA : ∀ a b : K, A (a+b)=A a* A b) (hA0 : A 0=1)
    (hB : ∀ a b : K, B (a+b)=B a*B b) (hB0 : B 0=1)
    (hAB : ∀ a b, Commute (A a) (B b)) (h w : G) (g : Kˣ) (l m : K)
    (hg : ∀ u : Kˣ, u ∈ Subgroup.zpowers g)
    (hg1 : (g : K) ≠ 1) (hm1 : m ≠ 1)
    (hScaleA : ∀ a, h*A a*h⁻¹=A a)
    (hScaleB : ∀ b, h*B b*h⁻¹=B ((g:K)*b))
    (hScaleA' : ∀ a, (w*h*w⁻¹)*A a*(w*h*w⁻¹)⁻¹=A (l*a))
    (hScaleB' : ∀ b, (w*h*w⁻¹)*B b*(w*h*w⁻¹)⁻¹=B (m*b))
    (hComm : Commute (w*h*w⁻¹) h)
    (H : Subgroup G) (hh : h∈H) (hy : A 1*B 1*w∈H) : ∀ a, B a∈H := by
  have hp := pure_second_root_mem A B hA hA0 hB hB0 hAB h w (g:K) l m
    hScaleA hScaleB hScaleA' hScaleB' hComm H hh hy
  have hn : (1-(g:K))*(1-m) ≠ 0 := mul_ne_zero
    (sub_ne_zero.mpr (Ne.symm hg1)) (sub_ne_zero.mpr (Ne.symm hm1))
  exact CFSGOrthogonalDGenerationPrimitiveRootSaturation.all_parameters_of_primitive_scaling
    B hB0 hB H h hh g hg hScaleB _ hn hp

end SymmetricSubgroupAsymptotics.CFSGUnequalTwoRootExtraction
