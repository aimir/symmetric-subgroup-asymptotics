import SymmetricSubgroupAsymptotics.PairedPermutations
import SymmetricSubgroupAsymptotics.BinaryPlaneFunctions

/-!
# The concrete critical permutation actions

The nonabelian actions use the actual binary Heisenberg coordinates. Their
normalizers preserve the unique nonidentity square, hence the paired flip.
-/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics

/-- Forward conjugation closure by a subgroup also gives backward closure. -/
theorem le_normalizer_of_conjugates {G : Type*} [Group G] (W H : Subgroup G)
    (hc : ∀ g ∈ W, ∀ h ∈ H, g * h * g⁻¹ ∈ H) : W ≤ Subgroup.normalizer H := by
  intro g hg
  apply Subgroup.mem_normalizer_iff.mpr
  intro h
  constructor
  · exact hc g hg h
  · intro hh
    have hh' := hc g⁻¹ (W.inv_mem hg) (g * h * g⁻¹) hh
    simpa [mul_assoc] using hh'

/-- The simultaneous flip is nonidentity on every nonempty paired set. -/
theorem pairedFlip_ne_one (α : Type*) [Nonempty α] : pairedFlip α ≠ 1 := by
  intro h
  obtain ⟨x⟩ := ‹Nonempty α›
  have he := congrArg Prod.snd (Equiv.congr_fun h (x, 0))
  simp [pairedFlip, pairedPermutation] at he

/-- A unique nonidentity square is fixed by every normalizing permutation. -/
theorem normalizer_le_centralizer_of_squares {G : Type*} [Group G]
    (H : Subgroup G) (z : G) (hz : z ≠ 1)
    (hs : ∀ h ∈ H, h ^ 2 = 1 ∨ h ^ 2 = z)
    (he : ∃ h ∈ H, h ^ 2 = z) :
    Subgroup.normalizer H ≤ Subgroup.centralizer {z} := by
  intro g hg
  obtain ⟨h, hh, hh2⟩ := he
  have hc := (Subgroup.mem_normalizer_iff.mp hg h).mp hh
  rcases hs (g * h * g⁻¹) hc with hs0 | hs1
  · rw [conj_pow, hh2] at hs0
    have heq := congrArg (fun x => g⁻¹ * x * g) hs0
    exact False.elim (hz (by simpa [mul_assoc] using heq))
  · rw [conj_pow, hh2] at hs1
    exact Subgroup.mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp hs1)

/-- Literal permutation image of the binary Heisenberg action. -/
def heisenbergPermutationGroup (m : ℕ) :
    Subgroup (Equiv.Perm ((Fin m → ZMod 2) × ZMod 2)) :=
  (BinaryHeisenberg.action m).range

theorem heisenbergPermutationGroup_card (m : ℕ) :
    Nat.card (heisenbergPermutationGroup m) = 2 ^ (2 * m + 1) := by
  rw [heisenbergPermutationGroup, Nat.card_congr
    (MonoidHom.ofInjective (BinaryHeisenberg.action_injective m)).toEquiv.symm]
  exact BinaryHeisenberg.card m

@[simp] theorem heisenberg_action_central_one (m : ℕ) :
    BinaryHeisenberg.action m (BinaryHeisenberg.central m (Multiplicative.ofAdd 1)) =
      pairedFlip (Fin m → ZMod 2) := by
  ext x i <;> simp [BinaryHeisenberg.action, BinaryHeisenberg.permutation,
    BinaryHeisenberg.central, pairedFlip, pairedPermutation]

theorem heisenberg_normalizer_le_pairedCentralizer {m : ℕ} (hm : 0 < m) :
    Subgroup.normalizer (heisenbergPermutationGroup m) ≤
      pairedCentralizer (Fin m → ZMod 2) := by
  apply normalizer_le_centralizer_of_squares _ _ (pairedFlip_ne_one _)
  · intro h hh
    obtain ⟨g, rfl⟩ := hh
    rw [← map_pow, BinaryHeisenberg.square]
    have hb : binaryDot g.b g.a = 0 ∨ binaryDot g.b g.a = 1 := by
      have h : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by decide
      exact h _
    rcases hb with hb | hb
    · left
      rw [hb]
      have hc : BinaryHeisenberg.central m (Multiplicative.ofAdd 0) = 1 := rfl
      rw [hc, map_one]
    · right
      rw [hb, heisenberg_action_central_one]
  · obtain ⟨g, hg⟩ := BinaryHeisenberg.kernel_square_surjective hm
      (BinaryHeisenberg.central m (Multiplicative.ofAdd 1))
      (by simp [BinaryHeisenberg.central, BinaryHeisenberg.quotient])
    refine ⟨BinaryHeisenberg.action m g, ⟨g, rfl⟩, ?_⟩
    rw [← map_pow, hg, heisenberg_action_central_one]

/-- The regular elementary abelian action, used for C2 and V4. -/
def regularBinaryAction (m : ℕ) :
    Multiplicative (Fin m → ZMod 2) →* Equiv.Perm (Fin m → ZMod 2) where
  toFun a :=
    { toFun := fun x => x + a.toAdd
      invFun := fun x => x - a.toAdd
      left_inv := by intro x; simp
      right_inv := by intro x; simp }
  map_one' := by ext x i; simp
  map_mul' a b := by ext x i; simp [add_comm, add_left_comm]

theorem regularBinaryAction_injective (m : ℕ) : Function.Injective (regularBinaryAction m) := by
  intro a b h
  have h0 := Equiv.congr_fun h 0
  simpa [regularBinaryAction] using h0

theorem regularBinaryAction_transitive {m : ℕ} (x y : Fin m → ZMod 2) :
    ∃ a : Multiplicative (Fin m → ZMod 2), regularBinaryAction m a x = y := by
  exact ⟨Multiplicative.ofAdd (y - x), by simp [regularBinaryAction]⟩

/-- The canonical binary quotient for each regular action is the identity. -/
def regularBinaryQuotient (m : ℕ) :
    Multiplicative (Fin m → ZMod 2) →* Multiplicative (Fin m → ZMod 2) := MonoidHom.id _

theorem regularBinaryQuotient_surjective (m : ℕ) :
    Function.Surjective (regularBinaryQuotient m) := Function.surjective_id

/-- The zero-dimensional kernel chart is an actual equivalence. -/
def regularBinaryKernelChart (m : ℕ) :
    Multiplicative (Fin 0 → ZMod 2) ≃* (regularBinaryQuotient m).ker where
  toFun _ := ⟨1, rfl⟩
  invFun _ := 1
  left_inv _ := Subsingleton.elim _ _
  right_inv x := Subtype.ext x.2.symm
  map_mul' _ _ := rfl

theorem regularBinaryQuotient_ker_central (m : ℕ) :
    (regularBinaryQuotient m).ker ≤ Subgroup.center (Multiplicative (Fin m → ZMod 2)) := by
  intro x hx
  have hx' : x = 1 := hx
  rw [hx']
  exact Subgroup.one_mem _

theorem regularBinaryQuotient_ker_le_frattini (m : ℕ) :
    (regularBinaryQuotient m).ker ≤ frattini (Multiplicative (Fin m → ZMod 2)) := by
  intro x hx
  have hx' : x = 1 := hx
  rw [hx']
  exact Subgroup.one_mem _

/-- The literal permutation subgroup of the regular binary action. -/
def regularBinaryPermutationGroup (m : ℕ) : Subgroup (Equiv.Perm (Fin m → ZMod 2)) :=
  (regularBinaryAction m).range

theorem regularBinaryPermutationGroup_card (m : ℕ) :
    Nat.card (regularBinaryPermutationGroup m) = 2 ^ m := by
  rw [regularBinaryPermutationGroup, Nat.card_congr
    (MonoidHom.ofInjective (regularBinaryAction_injective m)).toEquiv.symm]
  simp [Nat.card_eq_fintype_card]

theorem heisenbergPermutationGroup_le_pairedCentralizer (m : ℕ) :
    heisenbergPermutationGroup m ≤ pairedCentralizer (Fin m → ZMod 2) := by
  intro p hp
  obtain ⟨g, rfl⟩ := hp
  apply Subgroup.mem_centralizer_singleton_iff.mpr
  ext x i <;> simp [BinaryHeisenberg.action, BinaryHeisenberg.permutation,
    pairedFlip, pairedPermutation, add_assoc, add_comm, add_left_comm]

/-- The degree-four Heisenberg action is the entire paired centralizer. -/
theorem d8_eq_pairedCentralizer :
    heisenbergPermutationGroup 1 = pairedCentralizer (Fin 1 → ZMod 2) := by
  apply Subgroup.eq_of_le_of_card_ge (heisenbergPermutationGroup_le_pairedCentralizer 1)
  rw [heisenbergPermutationGroup_card, pairedCentralizer_card]
  norm_num

/-- The natural D8 normalizer is exactly D8. -/
theorem d8_normalizer_eq_pairedCentralizer :
    Subgroup.normalizer (heisenbergPermutationGroup 1) =
      pairedCentralizer (Fin 1 → ZMod 2) := by
  apply le_antisymm (heisenberg_normalizer_le_pairedCentralizer (by decide))
  rw [← d8_eq_pairedCentralizer]
  exact Subgroup.le_normalizer

private theorem e8_flip_conjugate (f : (Fin 2 → ZMod 2) → ZMod 2)
    (g : BinaryHeisenberg 2) :
    ∃ h : BinaryHeisenberg 2, BinaryHeisenberg.action 2 h =
      pairedPermutation (Equiv.refl _) f * BinaryHeisenberg.action 2 g *
        (pairedPermutation (Equiv.refl _) f)⁻¹ := by
  obtain ⟨b, c, hc⟩ := binaryPlane_derivative_affine f g.a
  refine ⟨⟨g.a, g.b + b, g.c + c⟩, ?_⟩
  apply Equiv.ext
  rintro ⟨x, z⟩
  apply Prod.ext
  · rfl
  · change z + binaryDot (g.b + b) x + (g.c + c) =
      z + f x + binaryDot g.b x + g.c + f (x + g.a)
    rw [binaryDot_add_left]
    linear_combination -(hc x)

private theorem e8_base_conjugate (σ : Equiv.Perm (Fin 2 → ZMod 2))
    (g : BinaryHeisenberg 2) :
    ∃ h : BinaryHeisenberg 2, BinaryHeisenberg.action 2 h =
      pairedPermutation σ 0 * BinaryHeisenberg.action 2 g * (pairedPermutation σ 0)⁻¹ := by
  obtain ⟨b, hb⟩ := binary_affine_function_coordinates
    (fun x => binaryDot g.b (σ.symm x)) (by
      intro x y
      change binaryDot g.b (σ.symm (x + y)) = _
      rw [binaryPlane_permutation_affine, binaryDot_add_right, binaryDot_add_right])
  refine ⟨⟨σ g.a + σ 0, b, g.c + binaryDot g.b (σ.symm 0)⟩, ?_⟩
  apply Equiv.ext
  rintro ⟨x, z⟩
  apply Prod.ext
  · change x + (σ g.a + σ 0) = σ (σ.symm x + g.a)
    rw [binaryPlane_permutation_affine, σ.apply_symm_apply]
    abel
  · change z + binaryDot b x + (g.c + binaryDot g.b (σ.symm 0)) =
      z + 0 + binaryDot g.b (σ.symm x) + g.c + 0
    rw [hb x]
    ring

/-- Every paired permutation normalizes the degree-eight plus-type action.
The proof retains the actual four-point affine map and each original flip
function; its finite differences are affine by the proved polynomial identity. -/
theorem pairedCentralizer_le_e8_normalizer :
    pairedCentralizer (Fin 2 → ZMod 2) ≤ Subgroup.normalizer (heisenbergPermutationGroup 2) := by
  apply le_normalizer_of_conjugates
  intro n hn p hp
  obtain ⟨g, rfl⟩ := hp
  obtain ⟨⟨σ, f⟩, he⟩ := (pairedCentralizerEquiv (Fin 2 → ZMod 2)).symm.surjective ⟨n, hn⟩
  have hn' : pairedPermutation σ f = n := congrArg Subtype.val he
  have hprod : pairedPermutation σ f =
      pairedPermutation σ 0 * pairedPermutation (Equiv.refl _) f := by
    ext x <;> simp [pairedPermutation]
  obtain ⟨g₁, hg₁⟩ := e8_flip_conjugate f g
  obtain ⟨g₂, hg₂⟩ := e8_base_conjugate σ g₁
  refine ⟨g₂, ?_⟩
  calc
    BinaryHeisenberg.action 2 g₂ =
        pairedPermutation σ 0 * BinaryHeisenberg.action 2 g₁ * (pairedPermutation σ 0)⁻¹ := hg₂
    _ = (pairedPermutation σ 0 * pairedPermutation (Equiv.refl _) f) *
        BinaryHeisenberg.action 2 g *
          (pairedPermutation σ 0 * pairedPermutation (Equiv.refl _) f)⁻¹ := by
      rw [hg₁]
      group
    _ = _ := by rw [← hprod, hn']

theorem e8_normalizer_eq_pairedCentralizer :
    Subgroup.normalizer (heisenbergPermutationGroup 2) =
      pairedCentralizer (Fin 2 → ZMod 2) :=
  le_antisymm (heisenberg_normalizer_le_pairedCentralizer (by decide))
    pairedCentralizer_le_e8_normalizer

theorem c2_permutationGroup_eq_top : regularBinaryPermutationGroup 1 = ⊤ := by
  apply Subgroup.eq_top_of_card_eq
  rw [regularBinaryPermutationGroup_card]
  norm_num [Nat.card_eq_fintype_card, Fintype.card_perm]

/-- Every permutation of four points normalizes the regular Klein action. -/
theorem v4_normalizer_eq_top : Subgroup.normalizer
    (regularBinaryPermutationGroup 2 : Set (Equiv.Perm (Fin 2 → ZMod 2))) = ⊤ := by
  apply top_unique
  apply le_normalizer_of_conjugates
  intro σ _ p hp
  obtain ⟨a, rfl⟩ := hp
  refine ⟨Multiplicative.ofAdd (σ a.toAdd + σ 0), ?_⟩
  apply Equiv.ext
  intro x
  change x + (σ a.toAdd + σ 0) = σ (σ.symm x + a.toAdd)
  rw [binaryPlane_permutation_affine, σ.apply_symm_apply]
  abel

/-- The original normalizer orders of the four critical actions. -/
theorem c2_normalizer_card : Nat.card (Subgroup.normalizer
    (regularBinaryPermutationGroup 1 : Set (Equiv.Perm (Fin 1 → ZMod 2)))) = 2 := by
  rw [c2_permutationGroup_eq_top]
  have ht : Subgroup.normalizer (Set.univ : Set (Equiv.Perm (Fin 1 → ZMod 2))) = ⊤ := by
    ext g
    change (∀ h : Equiv.Perm (Fin 1 → ZMod 2), h ∈ Set.univ ↔ g * h * g⁻¹ ∈ Set.univ) ↔ True
    simp
  rw [show (↑(⊤ : Subgroup (Equiv.Perm (Fin 1 → ZMod 2))) :
    Set (Equiv.Perm (Fin 1 → ZMod 2))) = Set.univ from rfl, ht]
  norm_num [Nat.card_eq_fintype_card, Fintype.card_perm]

theorem v4_normalizer_card : Nat.card (Subgroup.normalizer
    (regularBinaryPermutationGroup 2 : Set (Equiv.Perm (Fin 2 → ZMod 2)))) = 24 := by
  rw [v4_normalizer_eq_top]
  norm_num [Nat.card_eq_fintype_card, Fintype.card_perm]

theorem d8_normalizer_card : Nat.card (Subgroup.normalizer
    (heisenbergPermutationGroup 1 : Set (Equiv.Perm ((Fin 1 → ZMod 2) × ZMod 2)))) = 8 := by
  rw [d8_normalizer_eq_pairedCentralizer, pairedCentralizer_card]
  norm_num

theorem e8_normalizer_card : Nat.card (Subgroup.normalizer
    (heisenbergPermutationGroup 2 : Set (Equiv.Perm ((Fin 2 → ZMod 2) × ZMod 2)))) = 384 := by
  rw [e8_normalizer_eq_pairedCentralizer, pairedCentralizer_card]
  norm_num

end SymmetricSubgroupAsymptotics
