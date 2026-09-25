import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Tactic.Group

/-!
# Ordered right transversals along actual subnormal cyclic steps

The new coordinate is the most significant coordinate in the total order.
Only the lower subgroup is normalized by the new generator; the original
subgroup need not be normal in the whole group. These lemmas perform one
step from actual cyclic coset data. Constructing that data from an actual
p-group subgroup chain is a separate obligation.
-/
set_option autoImplicit false
namespace SymmetricSubgroupAsymptotics

variable {G ι : Type*} [Group G]

/-- The exact triangular right-coset transport used by leading terms. -/
def CosetTriangular (H : Subgroup G) (T : ι → G)
    (lt comparable : ι → ι → Prop) : Prop :=
  ∀ a b c, lt a b → comparable b c →
    ∃ h : G, h ∈ H ∧ ∃ e : ι,
      lt e c ∧ T a * (T b)⁻¹ * T c = h * T e

/-- Append the new cyclic step on the right of the old representative. -/
def cosetStepRep {p : ℕ} (T : ι → G) (x : G) (a : Fin p × ι) : G :=
  T a.2 * x ^ a.1.val

/-- The new, higher subgroup coordinate is compared first. -/
def cosetStepLT {p : ℕ} (lt : ι → ι → Prop) (a b : Fin p × ι) : Prop :=
  a.1 < b.1 ∨ a.1 = b.1 ∧ lt a.2 b.2

/-- Coordinatewise comparability, with the old relation retained. -/
def cosetStepComparable {p : ℕ} (r : ι → ι → Prop)
    (a b : Fin p × ι) : Prop :=
  a.1 ≤ b.1 ∧ r a.2 b.2

theorem cosetTriangular_base (H : Subgroup G) :
    CosetTriangular H (fun _ : Unit => (1 : G))
      (fun _ _ => False) (fun _ _ => True) := by
  intro a b c hab
  exact hab.elim

/-- The shared high tail cancels. The new normalizing generator can
change lower coordinates, all of which remain in the old subgroup. -/
theorem cosetTriangular_step {p : ℕ} (H K : Subgroup G)
    (T : ι → G) (x : G) (lt comparable : ι → ι → Prop)
    (hmem : ∀ a, T a ∈ K)
    (hfactor : ∀ y : G, y ∈ K → ∃ h : G, h ∈ H ∧ ∃ e : ι, y = h * T e)
    (hx : x ∈ Subgroup.normalizer K) (htri : CosetTriangular H T lt comparable) :
    CosetTriangular H (cosetStepRep (p := p) T x)
      (cosetStepLT lt) (cosetStepComparable comparable) := by
  intro a b c hab hbc
  rcases hbc with ⟨hbc₁, hbc₂⟩
  rcases hab with hab | ⟨hab₁, hab₂⟩
  · let d : Fin p := ⟨a.1.val + (c.1.val - b.1.val), by
      have hc := c.1.isLt
      change a.1.val < b.1.val at hab
      change b.1.val ≤ c.1.val at hbc₁
      omega⟩
    have hdc : d < c.1 := by
      change a.1.val + (c.1.val - b.1.val) < c.1.val
      change a.1.val < b.1.val at hab
      change b.1.val ≤ c.1.val at hbc₁
      omega
    let u : G := x ^ a.1.val * (x ^ b.1.val)⁻¹
    have hu : u ∈ Subgroup.normalizer (K : Set G) := by
      change x ^ a.1.val * (x ^ b.1.val)⁻¹ ∈ Subgroup.normalizer (K : Set G)
      exact (Subgroup.normalizer (K : Set G)).mul_mem
        ((Subgroup.normalizer (K : Set G)).pow_mem hx a.1.val)
        ((Subgroup.normalizer (K : Set G)).inv_mem
          ((Subgroup.normalizer (K : Set G)).pow_mem hx b.1.val))
    let D : G := T a.2 * (u * ((T b.2)⁻¹ * T c.2) * u⁻¹)
    have hD : D ∈ K := K.mul_mem (hmem a.2)
      ((Subgroup.mem_normalizer_iff.mp hu _).mp
        (K.mul_mem (K.inv_mem (hmem b.2)) (hmem c.2)))
    obtain ⟨h, hh, e, he⟩ := hfactor D hD
    have hpow : u * x ^ c.1.val = x ^ d.val := by
      have hc : c.1.val = b.1.val + (c.1.val - b.1.val) := by
        change b.1.val ≤ c.1.val at hbc₁
        omega
      change (x ^ a.1.val * (x ^ b.1.val)⁻¹) * x ^ c.1.val =
        x ^ (a.1.val + (c.1.val - b.1.val))
      have hsplit : x ^ c.1.val = x ^ b.1.val * x ^ (c.1.val - b.1.val) := by
        rw [← pow_add]
        rw [← hc]
      rw [hsplit, pow_add]
      group
    refine ⟨h, hh, (d, e), Or.inl hdc, ?_⟩
    change (T a.2 * x ^ a.1.val) * (T b.2 * x ^ b.1.val)⁻¹ *
        (T c.2 * x ^ c.1.val) = h * (T e * x ^ d.val)
    calc
      _ = D * (u * x ^ c.1.val) := by dsimp [D, u]; group
      _ = D * x ^ d.val := by rw [hpow]
      _ = h * (T e * x ^ d.val) := by rw [he, mul_assoc]
  · obtain ⟨h, hh, e, hec, he⟩ := htri a.2 b.2 c.2 hab₂ hbc₂
    refine ⟨h, hh, (c.1, e), Or.inr ⟨rfl, hec⟩, ?_⟩
    change (T a.2 * x ^ a.1.val) * (T b.2 * x ^ b.1.val)⁻¹ *
        (T c.2 * x ^ c.1.val) = h * (T e * x ^ c.1.val)
    rw [hab₁]
    calc
      _ = (T a.2 * (T b.2)⁻¹ * T c.2) * x ^ c.1.val := by group
      _ = h * (T e * x ^ c.1.val) := by rw [he, mul_assoc]

/-- Membership of the extended representatives uses the actual next
subgroup, rather than an ambient permutation group of the same degree. -/
theorem cosetStepRep_mem {p : ℕ} (K L : Subgroup G) (hKL : K ≤ L)
    (T : ι → G) (x : G) (hmem : ∀ a, T a ∈ K) (hx : x ∈ L)
    (a : Fin p × ι) : cosetStepRep T x a ∈ L :=
  L.mul_mem (hKL (hmem a.2)) (L.pow_mem hx _)

/-- Actual cyclic coset factorizations compose, even for a nonsplit
step: no assertion that x itself has order p is made. -/
theorem cosetStepRep_factor {p : ℕ} (H K L : Subgroup G)
    (T : ι → G) (x : G)
    (hfactor : ∀ y : G, y ∈ K → ∃ h : G, h ∈ H ∧ ∃ e : ι, y = h * T e)
    (hstep : ∀ y : G, y ∈ L →
      ∃ z : G, z ∈ K ∧ ∃ i : Fin p, y = z * x ^ i.val) :
    ∀ y : G, y ∈ L →
      ∃ h : G, h ∈ H ∧ ∃ a : Fin p × ι, y = h * cosetStepRep T x a := by
  intro y hy
  obtain ⟨z, hz, i, hi⟩ := hstep y hy
  obtain ⟨h, hh, e, he⟩ := hfactor z hz
  exact ⟨h, hh, (i, e), by simpa only [cosetStepRep, he, mul_assoc] using hi⟩

/-- Coset uniqueness is retained by the new cyclic step. The hypotheses
are actual uniqueness statements for H in K and K in the next subgroup. -/
theorem cosetStepRep_unique {p : ℕ} (H K : Subgroup G) (hHK : H ≤ K)
    (T : ι → G) (x : G) (hmem : ∀ a, T a ∈ K)
    (hunique : ∀ a b, T a * (T b)⁻¹ ∈ H → a = b)
    (hstep : ∀ i j : Fin p, x ^ i.val * (x ^ j.val)⁻¹ ∈ K → i = j)
    (a b : Fin p × ι)
    (hab : cosetStepRep T x a * (cosetStepRep T x b)⁻¹ ∈ H) : a = b := by
  have hp : x ^ a.1.val * (x ^ b.1.val)⁻¹ ∈ K := by
    have hh := K.mul_mem
      (K.mul_mem (K.inv_mem (hmem a.2)) (hHK hab)) (hmem b.2)
    have heq : (T a.2)⁻¹ * (cosetStepRep T x a * (cosetStepRep T x b)⁻¹) * T b.2 =
        x ^ a.1.val * (x ^ b.1.val)⁻¹ := by
      dsimp [cosetStepRep]
      group
    rwa [heq] at hh
  have hij := hstep a.1 b.1 hp
  have hlow : T a.2 * (T b.2)⁻¹ ∈ H := by
    have heq : cosetStepRep T x a * (cosetStepRep T x b)⁻¹ =
        T a.2 * (T b.2)⁻¹ := by
      dsimp [cosetStepRep]
      rw [hij]
      group
    rwa [heq] at hab
  exact Prod.ext hij (hunique a.2 b.2 hlow)

end SymmetricSubgroupAsymptotics
