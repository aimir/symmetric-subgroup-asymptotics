import SymmetricSubgroupAsymptotics.ZmudSemisimpleDualGenerators
import SymmetricSubgroupAsymptotics.PrimeSocleSemisimple
import SymmetricSubgroupAsymptotics.SocleNormalSubgroupGeneratorInheritance
import SymmetricSubgroupAsymptotics.SocleNormalGeneratorNumber

/-! The primal normal-generator tuple on a prime-primary socle gives a
tuple of dual vectors meeting every nonzero invariant subspace.  The
semisimplicity used here is that of the actual socle conjugation module,
not Maschke semisimplicity for the ambient group. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical MonoidAlgebra

namespace SymmetricSubgroupAsymptotics.ZmudPrimeSocleDualDetectors

/-- Normal generators of an original elementary kernel are generators of
its actual quotient module. -/
theorem originalKernel_generated
    {p : ℕ} [Fact p.Prime] {G B : Type} [Group G] [Group B]
    (pi : G →* B) (A : Rep (ZMod p) B)
    (C : OriginalKernelModuleChart pi A) {t : ℕ}
    (x : Fin t → G) (hx : Subgroup.normalClosure (Set.range x) = pi.ker) :
    RepresentationGeneratedBy A.ρ t := by
  have hxker (i : Fin t) : x i ∈ pi.ker := by
    rw [← hx]
    exact Subgroup.subset_normalClosure (Set.mem_range_self i)
  let v : Fin t → A.ρ.asModule := fun i =>
    (C.equiv.symm ⟨x i, hxker i⟩).toAdd
  let L : Submodule (ZMod p)[B] A.ρ.asModule :=
    Submodule.span (ZMod p)[B] (Set.range v)
  let T : Subrepresentation A.ρ := Subrepresentation.ofSubmodule' L
  let K : Subgroup G :=
    OriginalKernelQuotientChart.submoduleGroup pi A C T.toSubmodule
  letI : K.Normal :=
    OriginalKernelQuotientChart.submoduleGroup_normal pi A C T.toSubmodule
      (fun b _ hw => T.apply_mem_toSubmodule b hw)
  have hxK : ∀ i, x i ∈ K := by
    intro i
    have hv : v i ∈ L := Submodule.subset_span (Set.mem_range_self i)
    have hm := (OriginalKernelQuotientChart.chart_mem_submoduleGroup
      pi A C T.toSubmodule (C.equiv.symm ⟨x i, hxker i⟩)).mpr hv
    simpa only [MulEquiv.apply_symm_apply] using hm
  have hkerK : pi.ker ≤ K := by
    rw [← hx]
    apply Subgroup.normalClosure_le_normal
    rintro _ ⟨i, rfl⟩
    exact hxK i
  refine ⟨v, top_unique ?_⟩
  intro w _
  have hm : (C.equiv (Multiplicative.ofAdd w) : G) ∈ K :=
    hkerK (C.equiv (Multiplicative.ofAdd w)).2
  exact (OriginalKernelQuotientChart.chart_mem_submoduleGroup
    pi A C T.toSubmodule (Multiplicative.ofAdd w)).mp hm

/-- In a semisimple finite-dimensional representation, a generator bound
also gives that many linear forms which meet every nonzero invariant
subspace. -/
theorem exists_dual_detectors
    {k B V : Type} [Field k] [Group B] [AddCommGroup V] [Module k V]
    [FiniteDimensional k V] (rho : Representation k B V)
    [IsSemisimpleModule k[B] rho.asModule] {t : ℕ}
    (hgen : RepresentationGeneratedBy rho t) :
    ∃ l : Fin t → Module.Dual k V, ∀ S : Subrepresentation rho,
      S ≠ ⊥ → ∃ i v, v ∈ S ∧ l i v ≠ 0 := by
  obtain ⟨l, hl⟩ := ZmudSemisimpleDualGenerators.dual_generated rho hgen
  refine ⟨l, ?_⟩
  intro S hS
  by_contra hnot
  push Not at hnot
  let T := ZmudSemisimpleDualGenerators.annihilator rho S
  have hspan : Submodule.span k[B] (Set.range l) ≤ T.asSubmodule := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    change l i ∈ S.toSubmodule.dualAnnihilator
    rw [Submodule.mem_dualAnnihilator]
    intro v hv
    exact hnot i v hv
  have hT : T = ⊤ := by
    apply top_unique
    intro w _
    exact hspan (by rw [hl]; trivial)
  apply hS
  apply Subrepresentation.toSubmodule_injective
  apply Submodule.ext
  intro v
  constructor
  · intro hv
    apply (Submodule.mem_bot (R := k) (M := V)).mpr
    apply (Module.forall_dual_apply_eq_zero_iff k v).mp
    intro f
    have hf : f ∈ T := by rw [hT]; trivial
    exact (Submodule.mem_dualAnnihilator f).mp hf v hv
  · intro hv
    change v = 0 at hv
    exact hv ▸ S.toSubmodule.zero_mem

/-- The literal prime-primary socle has a dual detector tuple of length
bounded by the normal-generator tuple of the whole socle. -/
theorem primeSocle_exists_dual_detectors
    (p : ℕ) [Fact p.Prime]
    (G : Type) [Group G] [Finite G] (P : Subgroup G → Prop)
    {t : ℕ} (ht : SocleNormalGeneratorBound G t) :
    let C := selectedPrimeSoclePartElementaryChart (G := G) p P
    ∃ l : Fin t → Module.Dual (ZMod C.p) C.V,
      ∀ S : Subrepresentation C.quotientRepresentation.ρ,
        S ≠ ⊥ → ∃ i v, v ∈ S ∧ l i v ≠ 0 := by
  let E := minimalNormalSoclePart G (fun M => P M ∧ IsPGroup p M)
  let C := selectedPrimeSoclePartElementaryChart (G := G) p P
  let A := C.quotientRepresentation
  have hn : MarkedC4.normalGen E ≤ t :=
    (MarkedC4.normalGen_le_socle_of_normal_le E
      (minimalNormalSoclePart_le_finiteGroupSocle G _)).trans
        ((socleNormalGeneratorBound_iff_normalGen_le G t).mp ht)
  obtain ⟨x, hx⟩ := exists_normal_generating_tuple_of_normalGen_le E hn
  have hxker : Subgroup.normalClosure (Set.range x) =
      (QuotientGroup.mk' E).ker := by
    simpa only [QuotientGroup.ker_mk'] using hx
  have hgen : RepresentationGeneratedBy A.ρ t :=
    originalKernel_generated (QuotientGroup.mk' E) A C.originalKernelChart x hxker
  letI : IsSemisimpleModule (ZMod C.p)[G ⧸ E] A.ρ.asModule :=
    selectedPrimeSoclePart_quotientRepresentation_isSemisimple p P
  letI : FiniteDimensional (ZMod C.p) A := by
    change FiniteDimensional (ZMod C.p) C.V
    infer_instance
  exact exists_dual_detectors A.ρ hgen

end SymmetricSubgroupAsymptotics.ZmudPrimeSocleDualDetectors
