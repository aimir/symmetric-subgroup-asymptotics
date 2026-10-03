import SymmetricSubgroupAsymptotics.ActualWreathCompressionTower
import SymmetricSubgroupAsymptotics.NormalChiefSeries

/-!
# Existence of the actual wreath-compression tower

This file constructs the dependent tower by strong induction on the order of
the literal local component.  At every stage the local group is quotiented by
an actual minimal normal subgroup and the ambient group is quotiented by its
literal coordinate intersection.  The block top and the real block set never
change.

The only input at an abelian layer is the section-capacity estimate for the
actual correlated ambient module.  Nonabelian layers use the proved
semisimple subdirect chart.  In particular the construction applies without
change to local degree two and to local components which are 2-groups.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
open scoped Classical IsMulCommutative

namespace SymmetricSubgroupAsymptotics

variable {Q I : Type} [Group Q] [Fintype I] [Nonempty I]
  [MulAction Q I] [FaithfulSMul Q I]

/-- A capacity theorem applicable to every elementary local chief step of
the fixed actual block system.  The state may already be a quotient of the
original ambient action; the same block top and coordinate set are retained.
-/
def ActualWreathElementaryCapacityInput : Prop :=
  ∀ (S : ActualWreathCompressionState Q I)
    (D' : Type) [Group D'] [Finite D']
    (phi : S.D →* D') (_hphi : Function.Surjective phi)
    (C : ElementaryMinimalNormalChart phi.ker),
    ∃ H : ElementaryLayerJointCapacityBound C.p
      (QuotientGroup.mk'
        (PermutationalWreathProduct.Compression.kernel S.rho phi))
      (QuotientGroup.mk'_surjective
        (PermutationalWreathProduct.Compression.kernel S.rho phi))
      (PermutationalWreathProduct.Compression.kernelElementaryChart
        (p := C.p) S.rho phi C.equiv.symm S.rho_injective).quotientRepresentation
      (PermutationalWreathProduct.Compression.kernelElementaryChart
        (p := C.p) S.rho phi C.equiv.symm S.rho_injective).originalKernelChart,
      H.capacity ≤ Module.finrank (ZMod C.p) C.V * Fintype.card I / 2 ∧
      H.capacity ≤ traceyInducedGeneratorCeiling
        (Module.finrank (ZMod C.p) C.V) (Fintype.card I) ∧
      TraceyRefinedInducedCapacityBounds C.p
        (Module.finrank (ZMod C.p) C.V) (Fintype.card I) H.capacity ∧
      H.coefficient ≤
        (C.p : ℝ) ^ traceyAffineCoefficientExponent
          (Module.finrank (ZMod C.p) C.V) (Fintype.card I)
          (traceyInducedGeneratorCeiling
            (Module.finrank (ZMod C.p) C.V) (Fintype.card I))
          S.generatorCount S.sourceDegree C.p

namespace ActualWreathCompressionTower

private theorem chiefSeries_length_pos
    (G : Type) [Group G] [Finite G] [Nontrivial G]
    (s : ActualChiefSeries G) : 0 < s.length := by
  by_contra h
  have hs0 : s.length = 0 := Nat.eq_zero_of_not_pos h
  have hbt : (⊥ : Subgroup G) = ⊤ := by
    calc
      (⊥ : Subgroup G) = s.subgroup 0 := s.head.symm
      _ = s.subgroup (Fin.last s.length) := by
        congr 1
        ext
        simp [hs0]
      _ = ⊤ := s.last
  exact not_subsingleton G
    (Subgroup.subsingleton_iff.mp (subsingleton_iff_bot_eq_top.mp hbt))

private theorem firstChief_minimal
    (G : Type) [Group G] [Finite G] [Nontrivial G]
    (s : ActualChiefSeries G)
    (i0 : Fin s.length) (hi0 : i0.1 = 0)
    (E : Subgroup G) (hE : E = s.subgroup i0.succ) :
    E ≠ ⊥ ∧
      ∀ K : Subgroup G, K.Normal → K ≤ E → K = ⊥ ∨ K = E := by
  have hcast : i0.castSucc = (0 : Fin (s.length + 1)) := by
    ext
    exact hi0
  have hlow : s.subgroup i0.castSucc = ⊥ := by
    rw [hcast, s.head]
  have hne : E ≠ ⊥ := by
    intro he
    have hstep := s.step i0
    rw [hlow, ← hE, he] at hstep
    exact (lt_irrefl (⊥ : Subgroup G)) hstep
  refine ⟨hne, ?_⟩
  intro K hK hKE
  have h := s.chief i0 K hK (by rw [hlow]; exact bot_le)
    (by simpa [hE] using hKE)
  simpa [hlow, hE] using h

/-- Every faithful full-component wreath state admits an actual local-chief
compression tower, provided the published elementary induced-module
capacity is available at each literal abelian step. -/
theorem nonempty_of_capacity
    (H : ActualWreathElementaryCapacityInput (Q := Q) (I := I))
    (S : ActualWreathCompressionState Q I) :
    Nonempty (ActualWreathCompressionTower S) := by
  classical
  have hmain : ∀ n : ℕ,
      ∀ (S₀ : ActualWreathCompressionState Q I), Nat.card S₀.D = n →
        Nonempty (ActualWreathCompressionTower S₀) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro S₀ hcard
      rcases subsingleton_or_nontrivial S₀.D with hsub | hntriv
      · exact ⟨.terminal S₀ hsub⟩
      · letI : Nontrivial S₀.D := hntriv
        let s : ActualChiefSeries S₀.D := actualChiefSeries S₀.D
        have hlen : 0 < s.length := chiefSeries_length_pos S₀.D s
        let i0 : Fin s.length := ⟨0, hlen⟩
        let E : Subgroup S₀.D := s.subgroup i0.succ
        letI : E.Normal := s.normal i0.succ
        have hfirst := firstChief_minimal S₀.D s i0 rfl E rfl
        let D' := S₀.D ⧸ E
        let phi : S₀.D →* D' := QuotientGroup.mk' E
        have hphi : Function.Surjective phi := QuotientGroup.mk'_surjective E
        have hquot : Nat.card D' < Nat.card S₀.D := by
          rw [← E.index_eq_card, ← E.index_mul_card]
          exact lt_mul_of_one_lt_right
            (by rw [E.index_eq_card]; exact Nat.card_pos)
            (E.one_lt_card_iff_ne_bot.mpr hfirst.1)
        obtain ⟨next⟩ := ih (Nat.card D') (by omega)
          (S₀.quotient D' phi hphi) rfl
        have hker : phi.ker = E := QuotientGroup.ker_mk' E
        have hker_ne : phi.ker ≠ ⊥ := by simpa [hker] using hfirst.1
        have hker_min : ∀ K : Subgroup S₀.D,
            K.Normal → K ≤ phi.ker → K = ⊥ ∨ K = phi.ker := by
          intro K hK hle
          have hleE : K ≤ E := by simpa [hker] using hle
          rcases hfirst.2 K hK hleE with hbot | htop
          · exact Or.inl hbot
          · exact Or.inr (by simpa [hker] using htop)
        by_cases hcomm : IsMulCommutative phi.ker
        · obtain ⟨C⟩ := elementaryMinimalNormalChart_nonempty
            phi.ker hker_ne hcomm hker_min
          obtain ⟨HC, hhalf, hlog, hrefined, hcoeff⟩ :=
            H S₀ D' phi hphi C
          exact ⟨.elementary S₀ D' phi hphi C HC hhalf hlog hrefined hcoeff next⟩
        · let C := semisimpleNormalChart_of_nonabelian_minimal
            phi.ker hker_min hcomm
          exact ⟨.semisimple S₀ D' phi hphi C next⟩
  exact hmain (Nat.card S.D) S rfl

/-- Chosen tower spelling used by the affine-component transfer. -/
noncomputable def canonicalOfCapacity
    (H : ActualWreathElementaryCapacityInput (Q := Q) (I := I))
    (S : ActualWreathCompressionState Q I) :
    ActualWreathCompressionTower S :=
  Classical.choice (nonempty_of_capacity H S)

end ActualWreathCompressionTower
end SymmetricSubgroupAsymptotics

end
