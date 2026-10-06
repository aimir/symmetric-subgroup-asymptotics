import SymmetricSubgroupAsymptotics.PrimeMinimalNormalElementary
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeNineSocleGenerators
import SymmetricSubgroupAsymptotics.MinimalNormalCompositionCharts

/-!
# Elementary coordinates on a prime-primary socle part

A selected sum of ambient minimal normal `p`-subgroups is elementary
abelian.  Distinct ambient minimal normal subgroups commute because their
intersection is trivial; each individual factor is elementary by the
finite p-group center argument.  This gives literal prime-field coordinates
on the whole selected socle part, without choosing its simple factors.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical IsMulCommutative

namespace SymmetricSubgroupAsymptotics

variable (p : ℕ) [Fact p.Prime]
variable {G : Type} [Group G] [Finite G]
variable (P : Subgroup G → Prop)

private abbrev PrimeSocleFactors : Finset (Subgroup G) :=
  Finset.univ.filter (fun M : Subgroup G =>
    IsMinimalNormalSubgroup M ∧ P M ∧ IsPGroup p M)

private abbrev SelectedPrimeSoclePart : Subgroup G :=
  minimalNormalSoclePart G (fun M => P M ∧ IsPGroup p M)

omit [Fact p.Prime] in
private theorem primeSocleFactors_sup_eq :
    (PrimeSocleFactors p P).sup id = SelectedPrimeSoclePart p P := by
  unfold PrimeSocleFactors SelectedPrimeSoclePart minimalNormalSoclePart
  simp only

/-- Two selected prime-primary minimal normal factors commute elementwise.
For distinct factors, their intersection is an ambient-normal proper
subgroup of either factor and hence is trivial. -/
theorem selectedPrimeMinimalNormals_commutator_eq_bot
    (M K : Subgroup G)
    (hM : M ∈ PrimeSocleFactors p P)
    (hK : K ∈ PrimeSocleFactors p P) :
    ⁅M, K⁆ = ⊥ := by
  have hMd := (Finset.mem_filter.mp hM).2
  have hKd := (Finset.mem_filter.mp hK).2
  letI : M.Normal := hMd.1.1
  letI : K.Normal := hKd.1.1
  by_cases hMK : M = K
  · subst K
    have hcomm : IsMulCommutative M :=
      minimalNormal_isMulCommutative_of_isPGroup p M hMd.1 hMd.2.2
    exact (Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
      (Subgroup.le_centralizer_iff_isMulCommutative.mpr hcomm))
  · have hinf : M ⊓ K = ⊥ := by
      by_contra hne
      have hEq : M ⊓ K = M :=
        hMd.1.2.2 (M ⊓ K) inferInstance hne inf_le_left
      have hMleK : M ≤ K := by rw [← hEq]; exact inf_le_right
      have hMeqK : M = K :=
        hKd.1.2.2 M inferInstance hMd.1.2.1 hMleK
      exact hMK hMeqK
    apply le_antisymm
    · exact (Subgroup.commutator_le_inf (H₁ := M) (H₂ := K)).trans_eq hinf
    · exact bot_le

/-- A selected sum of ambient minimal normal `p`-subgroups is commutative. -/
theorem selectedPrimeSoclePart_isMulCommutative :
    IsMulCommutative (SelectedPrimeSoclePart p P) := by
  rw [← primeSocleFactors_sup_eq p P]
  apply Subgroup.le_centralizer_iff_isMulCommutative.mp
  apply Finset.sup_le
  intro M hM
  rw [Subgroup.le_centralizer_iff]
  apply Finset.sup_le
  intro K hK
  exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp
    (selectedPrimeMinimalNormals_commutator_eq_bot p P K M hK hM)

/-- Every element in a selected prime-primary socle part has exponent
`p`.  The proof works in the whole commutative sum and therefore does not
choose a product decomposition. -/
theorem selectedPrimeSoclePart_pow_prime_eq_one :
    ∀ x : SelectedPrimeSoclePart p P, x ^ p = 1 := by
  let A := SelectedPrimeSoclePart p P
  letI : IsMulCommutative A := selectedPrimeSoclePart_isMulCommutative p P
  let Z : Subgroup G := ((powMonoidHom (α := A) p).ker).map A.subtype
  have hAZ : A ≤ Z := by
    change SelectedPrimeSoclePart p P ≤ Z
    rw [← primeSocleFactors_sup_eq p P]
    apply Finset.sup_le
    intro M hM
    have hMd := (Finset.mem_filter.mp hM).2
    letI : M.Normal := hMd.1.1
    intro m hm
    have hmA : m ∈ A := by
      change m ∈ SelectedPrimeSoclePart p P
      rw [← primeSocleFactors_sup_eq p P]
      exact Finset.le_sup (f := id) hM hm
    let a : A := ⟨m, hmA⟩
    refine ⟨a, ?_, rfl⟩
    change a ^ p = 1
    apply Subtype.ext
    change m ^ p = 1
    exact congrArg Subtype.val
      (minimalNormal_pow_prime_eq_one_of_isPGroup p M hMd.1 hMd.2.2
        ⟨m, hm⟩)
  intro x
  obtain ⟨a, ha, hax⟩ := hAZ x.2
  have hEq : a = x := Subtype.ext hax
  subst a
  exact ha

/-- Literal elementary chart on any selected prime-primary socle part. -/
noncomputable def selectedPrimeSoclePartElementaryChart :
    ElementaryMinimalNormalChart (SelectedPrimeSoclePart p P) := by
  let A := SelectedPrimeSoclePart p P
  letI : IsMulCommutative A := selectedPrimeSoclePart_isMulCommutative p P
  letI : Module (ZMod p) (Additive A) :=
    AddCommGroup.zmodModule (n := p) (fun x => by
      apply Additive.toMul.injective
      exact selectedPrimeSoclePart_pow_prime_eq_one p P x.toMul)
  exact
    { p := p
      p_prime := Fact.out
      primeFact := inferInstance
      V := Additive A
      addCommGroup := inferInstance
      module := inferInstance
      finiteDimensional := Module.Finite.of_finite
      equiv := elementaryAdditiveChart A }

end SymmetricSubgroupAsymptotics

end
