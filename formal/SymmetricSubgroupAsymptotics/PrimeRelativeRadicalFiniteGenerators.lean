import SymmetricSubgroupAsymptotics.PrimeRelativeRadicalGenerators
import SymmetricSubgroupAsymptotics.FiniteQuotientInvariantCertificates

/-! Finite original-generator tests identify the whole-ambient relative
radical. The normal closure is essential in general: ordinary closure is
valid only when its normality in the original ambient group is proved.
No finite group, quotient order, or numerical rank hypothesis is required. -/
set_option autoImplicit false
noncomputable section
open scoped commutatorElement

namespace SymmetricSubgroupAsymptotics

variable (p : ℕ) [Fact p.Prime]
    {G ι κ : Type*} [Group G]
    (N : Subgroup G) [N.Normal]

/-- A normal candidate kills the entire relative radical once it kills
the displayed generator powers and mixed generator commutators. -/
theorem primeRelativeRadical_le_of_finite_generator_tests
    (ambient : ι → G) (hambient : Subgroup.closure (Set.range ambient)=⊤)
    (generators : κ → G) (hgenerators : Subgroup.closure (Set.range generators)=N)
    (R : Subgroup G) [R.Normal]
    (hpowers : ∀ i, (generators i)^p ∈ R)
    (hmixed : ∀ i j, ⁅generators i,ambient j⁆ ∈ R) :
    primeRelativeRadical p N ≤ R := by
  have hcenter : N ≤ quotientCenterPreimage R := by
    rw [← hgenerators]
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨i,rfl⟩
    exact (mem_quotientCenterPreimage_iff R ambient hambient _).mpr (hmixed i)
  have hcomm : ⁅N,(⊤ : Subgroup G)⁆ ≤ R := by
    apply Subgroup.commutator_le.mpr
    intro n hn g _
    have hc : QuotientGroup.mk' R n ∈ Subgroup.center (G ⧸ R) := hcenter hn
    apply (QuotientGroup.eq_one_iff (N := R) _).mp
    change (QuotientGroup.mk' R) ⁅n,g⁆=1
    rw [map_commutatorElement]
    apply commutatorElement_eq_one_iff_mul_comm.mpr
    exact (Subgroup.mem_center_iff.mp hc (QuotientGroup.mk' R g)).symm
  rw [primeRelativeRadical_eq_ambient_generator_pow_commutator p N generators hgenerators]
  apply sup_le _ hcomm
  apply (Subgroup.closure_le R).mpr
  rintro _ ⟨i,rfl⟩
  exact hpowers i

/-- The literal finite tuple uses the same original N-generators and
ambient generators. No conjugation action or source subgroup is replaced. -/
def primeRelativeFiniteGenerators (ambient : ι → G) (generators : κ → G) :
    κ ⊕ (κ × ι) → G :=
  Sum.elim (fun i => (generators i)^p) (fun ij => ⁅generators ij.1,ambient ij.2⁆)

theorem primeRelativeFiniteGenerators_mem
    (ambient : ι → G) (generators : κ → G)
    (hgenerators : Subgroup.closure (Set.range generators)=N)
    (i : κ ⊕ (κ × ι)) :
    primeRelativeFiniteGenerators p ambient generators i ∈ primeRelativeRadical p N := by
  have hmem (j : κ) : generators j ∈ N := by
    rw [← hgenerators]
    exact Subgroup.subset_closure (Set.mem_range_self j)
  rcases i with i | ⟨i,j⟩
  · exact pow_mem_primeRelativeRadical p N ⟨generators i,hmem i⟩
  · exact commutator_mem_primeRelativeRadical p N ⟨generators i,hmem i⟩ (ambient j)

/-- The finite tuple's NORMAL closure always is the exact original
relative radical. This does not assert that its ordinary closure is normal. -/
theorem primeRelativeRadical_eq_finite_generator_normalClosure
    (ambient : ι → G) (hambient : Subgroup.closure (Set.range ambient)=⊤)
    (generators : κ → G) (hgenerators : Subgroup.closure (Set.range generators)=N) :
    primeRelativeRadical p N =
      Subgroup.normalClosure (Set.range (primeRelativeFiniteGenerators p ambient generators)) := by
  apply le_antisymm
  · apply primeRelativeRadical_le_of_finite_generator_tests p N ambient hambient
      generators hgenerators
    · intro i
      exact Subgroup.subset_normalClosure (Set.mem_range_self (Sum.inl i))
    · intro i j
      exact Subgroup.subset_normalClosure (Set.mem_range_self (Sum.inr (i,j)))
  · apply Subgroup.normalClosure_le_normal
    rintro _ ⟨i,rfl⟩
    exact primeRelativeFiniteGenerators_mem p N ambient generators hgenerators i

/-- A finite Cayley producer may instead certify the ordinary closure,
provided it checks WHOLE-G normality under the original ambient generators. -/
theorem primeRelativeRadical_eq_finite_generator_closure
    (ambient : ι → G) (hambient : Subgroup.closure (Set.range ambient)=⊤)
    (generators : κ → G) (hgenerators : Subgroup.closure (Set.range generators)=N)
    [hR : (Subgroup.closure
      (Set.range (primeRelativeFiniteGenerators p ambient generators))).Normal] :
    primeRelativeRadical p N =
      Subgroup.closure (Set.range (primeRelativeFiniteGenerators p ambient generators)) := by
  apply le_antisymm
  · apply primeRelativeRadical_le_of_finite_generator_tests p N ambient hambient
      generators hgenerators
    · intro i
      exact Subgroup.subset_closure (Set.mem_range_self (Sum.inl i))
    · intro i j
      exact Subgroup.subset_closure (Set.mem_range_self (Sum.inr (i,j)))
  · apply (Subgroup.closure_le _).mpr
    rintro _ ⟨i,rfl⟩
    exact primeRelativeFiniteGenerators_mem p N ambient generators hgenerators i

end SymmetricSubgroupAsymptotics
