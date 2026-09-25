import SymmetricSubgroupAsymptotics.FusionKernelAssembly
import SymmetricSubgroupAsymptotics.FusionOrbitDeletion
import SymmetricSubgroupAsymptotics.FusionContinuationRow

/-!
# Canonical physical finite menus

Different original widths are placed in the same actual symmetric group.
The finite union is bounded from literal coverage, and each local family
keeps its original normalizer divisor and complete complement degree.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical
open Filter

namespace SymmetricSubgroupAsymptotics

/-- Relabel a family of actual subgroups, without quotienting by conjugacy. -/
def FusionRelabelledFamily {X Y : Type*} (e : X ≃ Y)
    (F : Set (Subgroup (Equiv.Perm X))) : Set (Subgroup (Equiv.Perm Y)) :=
  Set.range (fun H : F => relabelSubgroup e H.1)

theorem fusionRelabelledFamily_card {X Y : Type*} (e : X ≃ Y)
    (F : Set (Subgroup (Equiv.Perm X))) :
    Nat.card (FusionRelabelledFamily e F)=Nat.card F := by
  exact (Nat.card_congr (Equiv.ofInjective
    (fun H : F => relabelSubgroup e H.1)
    (fun _ _ h => Subtype.ext ((relabelSubgroup e).injective h)))).symm

/-- Canonical labels for one original orbit plus its complete complement. -/
def fusionMenuPointEquiv (h n : ℕ) (hn : 2*h≤n) :
    Fin (2*h) ⊕ Fin (n-2*h) ≃ Fin n :=
  finSumFinEquiv.trans (finCongr (by omega))

/-- The physical family is now literally a subset of subgroups of S_n. -/
def FusionCanonicalFamily {h n : ℕ} (U : Subgroup (Equiv.Perm (Fin (2*h))))
    (hn : 2*h≤n) (P : Subgroup (U × Equiv.Perm (Fin (n-2*h))) → Prop) :
    Set (Subgroup (Equiv.Perm (Fin n))) :=
  FusionRelabelledFamily (fusionMenuPointEquiv h n hn)
    (FusionOrbitFamily U (FusionAcceptedOrbitPredicate U P))

theorem fusionCanonicalFamily_card {h n : ℕ}
    (U : Subgroup (Equiv.Perm (Fin (2*h)))) (hn : 2*h≤n)
    (P : Subgroup (U × Equiv.Perm (Fin (n-2*h))) → Prop) :
    Nat.card (FusionCanonicalFamily U hn P)=
      Nat.card (FusionOrbitFamily U (FusionAcceptedOrbitPredicate U P)) :=
  fusionRelabelledFamily_card _ _

/-- A covering finite family yields the cardinal bound. Coverage
is literal subgroup membership, not an assumed numerical inequality. -/
theorem fusionPhysicalUnion_card_le {ι : Type*} [Fintype ι] {n : ℕ}
    (F : Set (Subgroup (Equiv.Perm (Fin n))))
    (A : ι → Set (Subgroup (Equiv.Perm (Fin n))))
    (hcover : ∀ H∈F, ∃ i, H∈A i) :
    Nat.card F ≤ ∑ i, Nat.card (A i) := by
  let B : Set (Subgroup (Equiv.Perm (Fin n))) := {H | ∃ i, H∈A i}
  have hFB : Nat.card F≤Nat.card B := Nat.card_le_card_of_injective
    (fun H : F => (⟨H.1,hcover H.1 H.2⟩ : B))
    (fun x y he => Subtype.ext (congrArg (fun z : B => z.1) he))
  let f : (Σ i, A i) → B := fun d => ⟨d.2.1,⟨d.1,d.2.2⟩⟩
  have hf : Function.Surjective f := by
    rintro ⟨H,i,hi⟩
    exact ⟨⟨i,H,hi⟩,rfl⟩
  have hBA := Nat.card_le_card_of_surjective f hf
  rw [Nat.card_sigma] at hBA
  exact hFB.trans hBA

section Menu

variable {ι : Type*} [Fintype ι] (h : ι → ℕ)
variable (U : ∀ i, Subgroup (Equiv.Perm (Fin (2*h i))))

/-- The finite index retains both the original action and every literal normal. -/
abbrev FusionPhysicalMenuAxis := Σ i, {N : Subgroup (U i) // N.Normal}

def fusionPhysicalMenuDivisor (i : ι) : ℝ :=
  Nat.card (Subgroup.normalizer (U i : Set (Equiv.Perm (Fin (2*h i)))))

omit [Fintype ι] in
theorem fusionPhysicalMenuDivisor_pos (i : ι) : 0<fusionPhysicalMenuDivisor h U i := by
  unfold fusionPhysicalMenuDivisor
  exact_mod_cast (Nat.card_pos (α := Subgroup.normalizer
    (U i : Set (Equiv.Perm (Fin (2*h i))))))

def fusionPhysicalMenuHot (v : ∀ i, {N : Subgroup (U i) // N.Normal} → ℕ)
    (D e : ∀ i, {N : Subgroup (U i) // N.Normal} → ℝ) (n : ℕ) : ℝ :=
  ∑ i, ∑ N : {N : Subgroup (U i) // N.Normal},
    fusionMenuHotKernel (fun m => (subgroupCount m : ℝ)) (n-2*h i) (h i) (v i N)
      (D i N) (fusionPhysicalMenuDivisor h U i) (e i N)

def fusionPhysicalMenuRow
    (D e : ∀ i, {N : Subgroup (U i) // N.Normal} → ℝ) (n b : ℕ) : ℝ :=
  fusionFiniteColdRow (fun j : FusionPhysicalMenuAxis h U => h j.1)
    (fun j => D j.1 j.2) (fun j => fusionPhysicalMenuDivisor h U j.1)
    (fun j => 16*e j.1 j.2) n b

/-- A finite actual covering menu gives the normalized forward recurrence.
Coverage, local surviving epi envelopes, and same-source moments are the
only family inputs. The original action/normal index is preserved in the
hot error and the cold row. Overlapping entries are allowed in this upper
bound; global disjoint ownership is a separate application obligation. -/
theorem fusionPhysicalUnion_recurrence
    (hh : ∀ i, 0<h i) (n : ℕ) (hn : ∀ i, 2*h i≤n)
    (F : Set (Subgroup (Equiv.Perm (Fin n))))
    (P : ∀ i, Subgroup (U i × Equiv.Perm (Fin (n-2*h i))) → Prop)
    (hP : ∀ i, FusionOrbitNatural (U i) (P i))
    (hcover : ∀ H∈F, ∃ i, H∈FusionCanonicalFamily (U i) (hn i) (P i))
    (v : ∀ i, {N : Subgroup (U i) // N.Normal} → ℕ)
    (D e : ∀ i, {N : Subgroup (U i) // N.Normal} → ℝ)
    (Φ : ∀ i, {N : Subgroup (U i) // N.Normal} →
      Subgroup (Equiv.Perm (Fin (n-2*h i))) → ℝ)
    (hD : ∀ i N, 0≤D i N) (he : ∀ i N, 0≤e i N)
    (hΦ : ∀ i N J, 0≤Φ i N J)
    (henvelope : ∀ i N J, fusionSurvivingEpiCount (U i) (P i) N J ≤
      fusionLocalFactor (n-2*h i) (h i) (v i N) (D i N) (e i N)*Φ i N J)
    (hmoment : ∀ i N q, 1≤q → (∑ J, Φ i N J^q) ≤
      (subgroupCount (n-2*h i+q*v i N) : ℝ)) :
    (Nat.card F : ℝ)/exactBenchmark n ≤
      fusionPhysicalMenuHot h U v D e n +
      ∑ b ∈ Finset.range n, fusionPhysicalMenuRow h U D e n b *
        ((subgroupCount b : ℝ)/exactBenchmark b) := by
  have hcard := fusionPhysicalUnion_card_le F
    (fun i => FusionCanonicalFamily (U i) (hn i) (P i)) hcover
  have hcardR : (Nat.card F : ℝ) ≤
      ∑ i, (Nat.card (FusionCanonicalFamily (U i) (hn i) (P i)) : ℝ) := by
    exact_mod_cast hcard
  have hlocal (i : ι) :
      (Nat.card (FusionCanonicalFamily (U i) (hn i) (P i)) : ℝ)/exactBenchmark n ≤
      ∑ N : {N : Subgroup (U i) // N.Normal},
        (fusionMenuHotKernel (fun m => (subgroupCount m : ℝ)) (n-2*h i) (h i) (v i N)
          (D i N) (fusionPhysicalMenuDivisor h U i) (e i N) +
        fusionColdKernel (n-2*h i) (h i) (D i N) (fusionPhysicalMenuDivisor h U i) (16*e i N) *
          ((subgroupCount (n-2*h i) : ℝ)/exactBenchmark (n-2*h i))) := by
    rw [fusionCanonicalFamily_card]
    have hx := fusionPhysical_kernel_bound (U i) (n-2*h i) (P i) (hP i)
      (v i) (D i) (e i) (Φ i) (hD i) (he i) (hΦ i) (henvelope i) (hmoment i)
    simpa only [Nat.sub_add_cancel (hn i),fusionPhysicalMenuDivisor] using hx
  calc
    _ ≤ (∑ i, (Nat.card (FusionCanonicalFamily (U i) (hn i) (P i)) : ℝ))/
        exactBenchmark n := div_le_div_of_nonneg_right hcardR (exactBenchmark_pos n).le
    _ = ∑ i, (Nat.card (FusionCanonicalFamily (U i) (hn i) (P i)) : ℝ)/
        exactBenchmark n := Finset.sum_div _ _ _
    _ ≤ ∑ i, ∑ N : {N : Subgroup (U i) // N.Normal},
        (fusionMenuHotKernel (fun m => (subgroupCount m : ℝ)) (n-2*h i) (h i) (v i N)
          (D i N) (fusionPhysicalMenuDivisor h U i) (e i N) +
        fusionColdKernel (n-2*h i) (h i) (D i N) (fusionPhysicalMenuDivisor h U i) (16*e i N) *
          ((subgroupCount (n-2*h i) : ℝ)/exactBenchmark (n-2*h i))) :=
      Finset.sum_le_sum (fun i _ => hlocal i)
    _ = _ := by
      simp only [Finset.sum_add_distrib]
      congr 1
      unfold fusionPhysicalMenuRow
      rw [fusionFiniteColdRow_weighted_sum
        (fun j : FusionPhysicalMenuAxis h U => h j.1)
        (fun j => D j.1 j.2) (fun j => fusionPhysicalMenuDivisor h U j.1)
        (fun j => 16*e j.1 j.2) (fun j => hh j.1) _ n (fun j => hn j.1)]
      rw [Fintype.sum_sigma]

/-- The installed physical continuation row is nonnegative. -/
theorem fusionPhysicalMenuRow_nonneg
    (D e : ∀ i, {N : Subgroup (U i) // N.Normal} → ℝ)
    (hD : ∀ i N, 0≤D i N) (n b : ℕ) : 0≤fusionPhysicalMenuRow h U D e n b :=
  fusionFiniteColdRow_nonneg (fun j : FusionPhysicalMenuAxis h U => h j.1)
    (fun j => D j.1 j.2) (fun j => fusionPhysicalMenuDivisor h U j.1)
    (fun j => 16*e j.1 j.2) (fun j => hD j.1 j.2)
    (fun j => fusionPhysicalMenuDivisor_pos h U j.1) n b

/-- Every entry deletes its original positive width from the actual degree. -/
theorem fusionPhysicalMenuRow_forward
    (D e : ∀ i, {N : Subgroup (U i) // N.Normal} → ℝ)
    (hh : ∀ i, 0<h i) {n b : ℕ} (hnb : n≤b) :
    fusionPhysicalMenuRow h U D e n b=0 :=
  fusionFiniteColdRow_forward (fun j : FusionPhysicalMenuAxis h U => h j.1)
    (fun j => D j.1 j.2) (fun j => fusionPhysicalMenuDivisor h U j.1)
    (fun j => 16*e j.1 j.2) (fun j => hh j.1) hnb

/-- The very same physical cold row has an exponentially small aggregate. -/
theorem fusionPhysicalMenuRow_decay
    (D e : ∀ i, {N : Subgroup (U i) // N.Normal} → ℝ)
    (hh : ∀ i, 0<h i) (hD : ∀ i N, 0≤D i N) (he : ∀ i N, 0<e i N) :
    ∃ C κ : ℝ, 0<C ∧ 0<κ ∧ ∀ᶠ n : ℕ in atTop,
      ∑ b ∈ Finset.range n, fusionPhysicalMenuRow h U D e n b ≤
        C*(2:ℝ)^(-κ*(n:ℝ)) :=
  fusionFiniteColdRow_decay (fun j : FusionPhysicalMenuAxis h U => h j.1)
    (fun j => D j.1 j.2) (fun j => fusionPhysicalMenuDivisor h U j.1)
    (fun j => 16*e j.1 j.2) (fun j => hh j.1) (fun j => hD j.1 j.2)
    (fun j => fusionPhysicalMenuDivisor_pos h U j.1) (fun j => by
      have := he j.1 j.2
      positivity)

/-- Contractivity is proved from local gaps before assuming any bound on
normalized total subgroup counts. -/
theorem fusionPhysicalMenuRow_contractive
    (D e : ∀ i, {N : Subgroup (U i) // N.Normal} → ℝ)
    (hh : ∀ i, 0<h i) (hD : ∀ i N, 0≤D i N) (he : ∀ i N, 0<e i N) :
    ∀ᶠ n : ℕ in atTop,
      ∑ b ∈ Finset.range n, fusionPhysicalMenuRow h U D e n b ≤ 1/2 :=
  fusionFiniteColdRow_contractive (fun j : FusionPhysicalMenuAxis h U => h j.1)
    (fun j => D j.1 j.2) (fun j => fusionPhysicalMenuDivisor h U j.1)
    (fun j => 16*e j.1 j.2) (fun j => hh j.1) (fun j => hD j.1 j.2)
    (fun j => fusionPhysicalMenuDivisor_pos h U j.1) (fun j => by
      have := he j.1 j.2
      positivity)

/-- The installed physical hot error is quadratically negligible. The
published coarse asymptotic is exposed as the only global counting input. -/
theorem fusionPhysicalMenuHot_decay
    (hs : FusionCoarseEstimate (fun n => (subgroupCount n : ℝ)))
    (v : ∀ i, {N : Subgroup (U i) // N.Normal} → ℕ)
    (D e : ∀ i, {N : Subgroup (U i) // N.Normal} → ℝ)
    (hD : ∀ i N, 0≤D i N) (he : ∀ i N, 0<e i N) :
    ∃ C κ : ℝ, 0<C ∧ 0<κ ∧ ∀ᶠ n : ℕ in atTop,
      fusionPhysicalMenuHot h U v D e n ≤ C*(2:ℝ)^(-κ*(n:ℝ)^2) := by
  obtain ⟨C,κ,hC,hκ,hbound⟩ := fusionMenuHotKernel_shifted_finite_sum
    (fun n => (subgroupCount n : ℝ)) hs
    (fun j : FusionPhysicalMenuAxis h U => h j.1) (fun j => v j.1 j.2)
    (fun j => D j.1 j.2) (fun j => fusionPhysicalMenuDivisor h U j.1)
    (fun j => e j.1 j.2) (fun j => hD j.1 j.2)
    (fun j => fusionPhysicalMenuDivisor_pos h U j.1) (fun j => he j.1 j.2)
  refine ⟨C,κ,hC,hκ,?_⟩
  filter_upwards [hbound] with n hn
  simpa only [fusionPhysicalMenuHot,Fintype.sum_sigma] using hn

end Menu

end SymmetricSubgroupAsymptotics
