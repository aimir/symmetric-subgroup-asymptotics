import SymmetricSubgroupAsymptotics.CFSGAdditiveRootExtraction

/-! A genuine two-root filter: one torus fixes the first commuting root
and scales the second. Its commuting Weyl conjugate may act differently
on the first root, but the actual double commutator eliminates that
coordinate exactly and retains a nonzero square factor in the second. -/
set_option autoImplicit false
noncomputable section
open scoped commutatorElement
namespace SymmetricSubgroupAsymptotics.CFSGTwoRootExtraction
variable {K G : Type*} [Field K] [Group G]

def pairScale (a b : K) : K × K →+ K × K where
  toFun v := (a * v.1, b * v.2)
  map_zero' := by ext <;> exact mul_zero _
  map_add' v w := by ext <;> simp only [Prod.fst_add, Prod.snd_add, mul_add]

theorem two_root_double_commutator (A B : K → G)
    (hA : ∀ a b : K, A (a + b) = A a * A b) (hA0 : A 0 = 1)
    (hB : ∀ a b : K, B (a + b) = B a * B b) (hB0 : B 0 = 1)
    (hAB : ∀ a b : K, Commute (A a) (B b))
    (h w : G) (k l : K)
    (hScaleA : ∀ a, h * A a * h⁻¹ = A a)
    (hScaleB : ∀ b, h * B b * h⁻¹ = B (k * b))
    (hScaleA' : ∀ a, (w * h * w⁻¹) * A a * (w * h * w⁻¹)⁻¹ = A (l * a))
    (hScaleB' : ∀ b, (w * h * w⁻¹) * B b * (w * h * w⁻¹)⁻¹ = B (k * b))
    (hComm : Commute (w * h * w⁻¹) h) :
    ⁅(A 1 * B 1 * w) * h * (A 1 * B 1 * w)⁻¹, h⁆ = B ((1 - k) ^ 2) := by
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
  have hs' : ∀ v, (w * h * w⁻¹) * root v * (w * h * w⁻¹)⁻¹ = root (pairScale l k v) := by
    intro v
    change (w * h * w⁻¹) * (A v.1 * B v.2) * (w * h * w⁻¹)⁻¹ = A (l * v.1) * B (k * v.2)
    calc
      (w * h * w⁻¹) * (A v.1 * B v.2) * (w * h * w⁻¹)⁻¹ =
          ((w * h * w⁻¹) * A v.1 * (w * h * w⁻¹)⁻¹) *
          ((w * h * w⁻¹) * B v.2 * (w * h * w⁻¹)⁻¹) := by group
      _ = A (l * v.1) * B (k * v.2) := by rw [hScaleA', hScaleB']
  have he : ((1, 1) : K × K) - pairScale l k (1, 1) -
      pairScale 1 k ((1, 1) - pairScale l k (1, 1)) = (0, (1 - k) ^ 2) := by
    ext
    · change (1 : K) - l * 1 - 1 * (1 - l * 1) = 0
      ring
    · change (1 : K) - k * 1 - k * (1 - k * 1) = (1 - k) ^ 2
      ring
  have h := CFSGAdditiveRootExtraction.double_commutator root hAdd hZero h w
    (pairScale 1 k) (pairScale l k) (1, 1) hs hs' hComm
  rw [he] at h
  simpa only [root, hA0, one_mul] using h

theorem pure_second_root_mem (A B : K → G)
    (hA : ∀ a b : K, A (a + b) = A a * A b) (hA0 : A 0 = 1)
    (hB : ∀ a b : K, B (a + b) = B a * B b) (hB0 : B 0 = 1)
    (hAB : ∀ a b : K, Commute (A a) (B b))
    (h w : G) (k l : K)
    (hScaleA : ∀ a, h * A a * h⁻¹ = A a)
    (hScaleB : ∀ b, h * B b * h⁻¹ = B (k * b))
    (hScaleA' : ∀ a, (w * h * w⁻¹) * A a * (w * h * w⁻¹)⁻¹ = A (l * a))
    (hScaleB' : ∀ b, (w * h * w⁻¹) * B b * (w * h * w⁻¹)⁻¹ = B (k * b))
    (hComm : Commute (w * h * w⁻¹) h)
    (H : Subgroup G) (hh : h ∈ H) (hy : A 1 * B 1 * w ∈ H) : B ((1 - k) ^ 2) ∈ H := by
  rw [← two_root_double_commutator A B hA hA0 hB hB0 hAB h w k l
    hScaleA hScaleB hScaleA' hScaleB' hComm, commutatorElement_def]
  have hx := H.mul_mem (H.mul_mem hy hh) (H.inv_mem hy)
  exact H.mul_mem (H.mul_mem (H.mul_mem hx hh) (H.inv_mem hx)) (H.inv_mem hh)

end SymmetricSubgroupAsymptotics.CFSGTwoRootExtraction
