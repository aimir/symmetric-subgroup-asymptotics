import SymmetricSubgroupAsymptotics.AllLifts
import Mathlib.GroupTheory.Perm.Centralizer
import Mathlib.GroupTheory.Frattini

/-! Concrete binary Heisenberg groups and their faithful permutation actions. -/

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace SymmetricSubgroupAsymptotics

/-- The binary dot product used by the concrete plus-type actions. -/
def binaryDot {m : ℕ} (b a : Fin m → ZMod 2) : ZMod 2 := ∑ i, b i * a i

@[simp] theorem binaryDot_zero_left {m : ℕ} (a : Fin m → ZMod 2) : binaryDot 0 a = 0 := by
  simp [binaryDot]

@[simp] theorem binaryDot_zero_right {m : ℕ} (b : Fin m → ZMod 2) : binaryDot b 0 = 0 := by
  simp [binaryDot]

@[simp] theorem binaryDot_add_left {m : ℕ} (a b c : Fin m → ZMod 2) :
    binaryDot (a + b) c = binaryDot a c + binaryDot b c := by
  simp [binaryDot, add_mul, Finset.sum_add_distrib]

@[simp] theorem binaryDot_add_right {m : ℕ} (a b c : Fin m → ZMod 2) :
    binaryDot a (b + c) = binaryDot a b + binaryDot a c := by
  simp [binaryDot, mul_add, Finset.sum_add_distrib]

@[simp] theorem binary_add_self (a : ZMod 2) : a + a = 0 := by
  have h : ∀ x : ZMod 2, x + x = 0 := by decide
  exact h a

@[simp] theorem binary_add_self_left (a b : ZMod 2) : a + (a + b) = b := by
  rw [← add_assoc, binary_add_self, zero_add]

/-- Coordinates `(a,b,c)` with multiplication dictated by their action
`(x,z) ↦ (x+a,z+b·x+c)`. -/
@[ext] structure BinaryHeisenberg (m : ℕ) where
  a : Fin m → ZMod 2
  b : Fin m → ZMod 2
  c : ZMod 2
  deriving Fintype, DecidableEq

namespace BinaryHeisenberg

instance (m : ℕ) : Mul (BinaryHeisenberg m) :=
  ⟨fun g h => ⟨g.a + h.a, g.b + h.b, g.c + h.c + binaryDot g.b h.a⟩⟩
instance (m : ℕ) : One (BinaryHeisenberg m) := ⟨⟨0, 0, 0⟩⟩
instance (m : ℕ) : Inv (BinaryHeisenberg m) :=
  ⟨fun g => ⟨g.a, g.b, g.c + binaryDot g.b g.a⟩⟩

instance (m : ℕ) : Group (BinaryHeisenberg m) := Group.ofLeftAxioms
  (by
    intro g h k
    apply BinaryHeisenberg.ext
    · change (g.a + h.a) + k.a = g.a + (h.a + k.a)
      exact add_assoc _ _ _
    · change (g.b + h.b) + k.b = g.b + (h.b + k.b)
      exact add_assoc _ _ _
    · change (g.c + h.c + binaryDot g.b h.a) + k.c + binaryDot (g.b + h.b) k.a =
        g.c + (h.c + k.c + binaryDot h.b k.a) + binaryDot g.b (h.a + k.a)
      simp only [binaryDot_add_left, binaryDot_add_right]
      ring)
  (by
    intro g
    apply BinaryHeisenberg.ext
    · change 0 + g.a = g.a
      simp
    · change 0 + g.b = g.b
      simp
    · change 0 + g.c + binaryDot 0 g.a = g.c
      simp)
  (by
    intro g
    apply BinaryHeisenberg.ext
    · change g.a + g.a = 0
      funext i
      exact binary_add_self _
    · change g.b + g.b = 0
      funext i
      exact binary_add_self _
    · change g.c + binaryDot g.b g.a + g.c + binaryDot g.b g.a = 0
      calc
        _ = (g.c + g.c) + (binaryDot g.b g.a + binaryDot g.b g.a) := by ring
        _ = 0 := by simp)

@[simp] theorem mul_a {m : ℕ} (g h : BinaryHeisenberg m) : (g * h).a = g.a + h.a := rfl
@[simp] theorem mul_b {m : ℕ} (g h : BinaryHeisenberg m) : (g * h).b = g.b + h.b := rfl
@[simp] theorem mul_c {m : ℕ} (g h : BinaryHeisenberg m) :
    (g * h).c = g.c + h.c + binaryDot g.b h.a := rfl
@[simp] theorem one_a (m : ℕ) : (1 : BinaryHeisenberg m).a = 0 := rfl
@[simp] theorem one_b (m : ℕ) : (1 : BinaryHeisenberg m).b = 0 := rfl
@[simp] theorem one_c (m : ℕ) : (1 : BinaryHeisenberg m).c = 0 := rfl

/-- The action on `2^(m+1)` actual points. -/
def permutation {m : ℕ} (g : BinaryHeisenberg m) : Equiv.Perm ((Fin m → ZMod 2) × ZMod 2) where
  toFun x := (x.1 + g.a, x.2 + binaryDot g.b x.1 + g.c)
  invFun x := (x.1 + g.a, x.2 + binaryDot g.b (x.1 + g.a) + g.c)
  left_inv x := by
    ext i <;> simp [add_comm, add_left_comm]
  right_inv x := by
    ext i <;> simp [add_comm, add_left_comm]

/-- Multiplication in the coordinate group is actual permutation composition. -/
def action (m : ℕ) : BinaryHeisenberg m →* Equiv.Perm ((Fin m → ZMod 2) × ZMod 2) where
  toFun := permutation
  map_one' := by ext x i <;> simp [permutation]
  map_mul' g h := by
    ext x i <;> simp [permutation, add_assoc, add_comm, add_left_comm]

@[simp] theorem binaryDot_single_right {m : ℕ} (b : Fin m → ZMod 2) (i : Fin m) :
    binaryDot b (Pi.single i 1) = b i := by
  simp [binaryDot, Pi.single_apply, mul_ite]

/-- Distinct group coordinates act as distinct literal permutations. -/
theorem action_injective (m : ℕ) : Function.Injective (action m) := by
  intro g h he
  have hz := Equiv.congr_fun he (0, 0)
  have ha : g.a = h.a := by simpa [action, permutation] using congrArg Prod.fst hz
  have hc : g.c = h.c := by simpa [action, permutation] using congrArg Prod.snd hz
  apply BinaryHeisenberg.ext ha _ hc
  funext i
  have hi := congrArg Prod.snd (Equiv.congr_fun he (Pi.single i 1, 0))
  simpa [action, permutation, hc] using hi

/-- The concrete action is transitive on its `2^(m+1)` points. -/
theorem action_transitive {m : ℕ} (x y : (Fin m → ZMod 2) × ZMod 2) :
    ∃ g : BinaryHeisenberg m, action m g x = y := by
  refine ⟨⟨y.1 - x.1, 0, y.2 - x.2⟩, ?_⟩
  simp [action, permutation]

/-- The original binary quotient records both translation and linear-shear
coordinates. -/
def quotient (m : ℕ) :
    BinaryHeisenberg m →* Multiplicative ((Fin m → ZMod 2) × (Fin m → ZMod 2)) where
  toFun g := Multiplicative.ofAdd (g.a, g.b)
  map_one' := rfl
  map_mul' _ _ := rfl

theorem quotient_surjective (m : ℕ) : Function.Surjective (quotient m) := by
  intro v
  exact ⟨⟨v.toAdd.1, v.toAdd.2, 0⟩, rfl⟩

@[simp] theorem mem_quotient_ker {m : ℕ} (g : BinaryHeisenberg m) :
    g ∈ (quotient m).ker ↔ g.a = 0 ∧ g.b = 0 := by
  change (g.a, g.b) = (0, 0) ↔ _
  simp only [Prod.mk.injEq]

/-- The central binary coordinate as an actual group homomorphism. -/
def central (m : ℕ) : Multiplicative (ZMod 2) →* BinaryHeisenberg m where
  toFun z := ⟨0, 0, z.toAdd⟩
  map_one' := rfl
  map_mul' z w := by ext <;> simp

/-- The original kernel chart is the literal central coordinate. -/
def kernelChart (m : ℕ) : Multiplicative (ZMod 2) ≃* (quotient m).ker where
  toFun z := ⟨central m z, by simp [central, quotient]⟩
  invFun g := Multiplicative.ofAdd g.1.c
  left_inv _ := rfl
  right_inv g := by
    apply Subtype.ext
    rcases mem_quotient_ker g.1 |>.mp g.2 with ⟨ha, hb⟩
    ext <;> simp [central, ha, hb]
  map_mul' z w := Subtype.ext ((central m).map_mul z w)

theorem quotient_ker_central (m : ℕ) : (quotient m).ker ≤ Subgroup.center (BinaryHeisenberg m) := by
  intro g hg
  rcases (mem_quotient_ker g).mp hg with ⟨ha, hb⟩
  rw [Subgroup.mem_center_iff]
  intro h
  ext <;> simp [ha, hb, add_comm]

/-- The square map on the binary quotient is exactly the plus-type form
`a·b`, in the retained central coordinate. -/
theorem square {m : ℕ} (g : BinaryHeisenberg m) :
    g ^ 2 = central m (Multiplicative.ofAdd (binaryDot g.b g.a)) := by
  rw [pow_two]
  ext i <;> simp [central]

/-- Exact group order of the concrete coordinate model. -/
theorem card (m : ℕ) : Nat.card (BinaryHeisenberg m) = 2 ^ (2 * m + 1) := by
  let e : BinaryHeisenberg m ≃ (Fin m → ZMod 2) × (Fin m → ZMod 2) × ZMod 2 :=
    { toFun := fun g => (g.a, g.b, g.c)
      invFun := fun g => ⟨g.1, g.2.1, g.2.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Nat.card_congr e]
  simp only [Nat.card_eq_fintype_card, Fintype.card_prod, Fintype.card_fun,
    Fintype.card_fin, ZMod.card]
  rw [show 2 * m + 1 = m + (m + 1) by omega, pow_add, pow_succ]

theorem point_card (m : ℕ) :
    Nat.card ((Fin m → ZMod 2) × ZMod 2) = 2 ^ (m + 1) := by
  simp [Nat.card_eq_fintype_card, pow_succ]

theorem quotient_finrank (m : ℕ) :
    Module.finrank (ZMod 2) ((Fin m → ZMod 2) × (Fin m → ZMod 2)) = 2 * m := by
  simp [Module.finrank_prod, two_mul]

@[simp] theorem binaryDot_single_left {m : ℕ} (a : Fin m → ZMod 2) (i : Fin m) :
    binaryDot (Pi.single i 1) a = a i := by
  simp [binaryDot, Pi.single_apply, ite_mul]

/-- The kernel is exactly the group centre, not only a central subgroup. -/
theorem center_eq_quotient_ker (m : ℕ) :
    Subgroup.center (BinaryHeisenberg m) = (quotient m).ker := by
  apply le_antisymm _ (quotient_ker_central m)
  intro g hg
  apply (mem_quotient_ker g).mpr
  have hc := Subgroup.mem_center_iff.mp hg
  constructor
  · funext i
    have hi := congrArg BinaryHeisenberg.c (hc (⟨0, Pi.single i 1, 0⟩ : BinaryHeisenberg m))
    simpa using hi
  · funext i
    have hi := congrArg BinaryHeisenberg.c (hc (⟨Pi.single i 1, 0, 0⟩ : BinaryHeisenberg m))
    simpa using hi.symm

/-- Every element of the central kernel is an actual square when `m>0`. -/
theorem kernel_square_surjective {m : ℕ} (hm : 0 < m)
    (z : BinaryHeisenberg m) (hz : z ∈ (quotient m).ker) :
    ∃ g : BinaryHeisenberg m, g ^ 2 = z := by
  let i : Fin m := ⟨0, hm⟩
  refine ⟨⟨Pi.single i 1, Pi.single i z.c, 0⟩, ?_⟩
  rw [square]
  rcases (mem_quotient_ker z).mp hz with ⟨ha, hb⟩
  ext <;> simp [central, ha, hb]

/-- Full quotient image forces the actual subgroup to contain the central
kernel: the nontrivial square cannot be omitted. -/
theorem full_quotient_iff {m : ℕ} (hm : 0 < m) (H : Subgroup (BinaryHeisenberg m)) :
    H.map (quotient m) = ⊤ ↔ H = ⊤ := by
  constructor
  · intro hH
    have hs := squares_mem_of_lift (quotient m) (quotient_ker_central m)
      (binaryKernelChart_pow_two (quotient m) (kernelChart m)) binary_mul_pow_two
      (H ⊓ (quotient m).ker) H hH rfl
    have hk : (quotient m).ker ≤ H := by
      intro z hz
      obtain ⟨g, rfl⟩ := kernel_square_surjective hm z hz
      exact (hs g).1
    exact (map_eq_top_iff_of_ker_le (quotient m) (quotient_surjective m) H hk).mp hH
  · rintro rfl
    exact Subgroup.map_top_of_surjective _ (quotient_surjective m)

/-- The central kernel lies in the Frattini subgroup, proved by the actual
full-image property rather than assumed from a classification theorem. -/
theorem quotient_ker_le_frattini {m : ℕ} (hm : 0 < m) :
    (quotient m).ker ≤ frattini (BinaryHeisenberg m) := by
  rw [frattini, Order.radical]
  apply le_iInf
  intro H
  apply le_iInf
  intro hH
  by_cases hk : (quotient m).ker ≤ H
  · exact hk
  · have hsup : H ⊔ (quotient m).ker = ⊤ := hH.2 _ (left_lt_sup.mpr hk)
    have hfull := (map_eq_top_iff_sup_kernel (quotient m) (quotient_surjective m) H).mpr hsup
    exact False.elim (hH.1 ((full_quotient_iff hm H).mp hfull))

end BinaryHeisenberg
end SymmetricSubgroupAsymptotics
