import SymmetricSubgroupAsymptotics.CFSGSymplecticProjectiveRootLift

/-! Faithful natural root parameters and projective-point labels in
the original central quotient. Equality lifts are proved from the
actual common fixed vector; no recognition certificate is supplied. -/
set_option autoImplicit false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGSymplecticTransvectionGeometry
open CFSGSymplecticSerreMatrices
variable {K : Type} [Field K]

def projectiveNaturalRootHom (r : ℕ) (hr : 0 < r) (v : Index (r + 1) → K) :
    Multiplicative K →* elementaryProjective K (r + 1) :=
  (QuotientGroup.mk' (Subgroup.center (elementaryRootGroup K (r + 1)))).comp
    (actualNaturalRootHom r hr v)

def projectiveNaturalRootLine (r : ℕ) (hr : 0 < r) (v : Index (r + 1) → K) :
    Subgroup (elementaryProjective K (r + 1)) := (projectiveNaturalRootHom r hr v).range

theorem projectiveNaturalRootHom_injective (r : ℕ) (hr : 0 < r)
    (v : Index (r + 1) → K) (hv : v ≠ 0) :
    Function.Injective (projectiveNaturalRootHom r hr v) := by
  intro a b he
  apply actualNaturalRootHom_injective r hr v hv
  exact actualNaturalRootElement_eq_of_projective_eq r hr v v a.toAdd b.toAdd he

def projectiveNaturalRootLineEquiv (r : ℕ) (hr : 0 < r)
    (v : Index (r + 1) → K) (hv : v ≠ 0) :
    Multiplicative K ≃* projectiveNaturalRootLine r hr v :=
  MonoidHom.ofInjective (projectiveNaturalRootHom_injective r hr v hv)

theorem projectiveNaturalRootLine_card (r : ℕ) (hr : 0 < r)
    (v : Index (r + 1) → K) (hv : v ≠ 0) :
    Nat.card (projectiveNaturalRootLine r hr v) = Nat.card K := by
  calc
    Nat.card (projectiveNaturalRootLine r hr v) = Nat.card (Multiplicative K) :=
      Nat.card_congr (projectiveNaturalRootLineEquiv r hr v hv).symm.toEquiv
    _ = Nat.card K := Nat.card_congr Multiplicative.toAdd

theorem projectiveNaturalRootLine_smul (r : ℕ) (hr : 0 < r)
    (v : Index (r + 1) → K) (c : K) (hc : c ≠ 0) :
    projectiveNaturalRootLine r hr (c • v) = projectiveNaturalRootLine r hr v := by
  let q := QuotientGroup.mk' (Subgroup.center (elementaryRootGroup K (r + 1)))
  ext T
  constructor
  · rintro ⟨a, rfl⟩
    refine ⟨Multiplicative.ofAdd (a.toAdd * c ^ 2), ?_⟩
    exact congrArg q (actualNaturalRootElement_smul r hr v c a.toAdd).symm
  · rintro ⟨a, rfl⟩
    refine ⟨Multiplicative.ofAdd (a.toAdd / c ^ 2), ?_⟩
    change q (actualNaturalRootElement r hr (c • v) (a.toAdd / c ^ 2)) =
      q (actualNaturalRootElement r hr v a.toAdd)
    rw [actualNaturalRootElement_smul, div_mul_cancel₀ _ (pow_ne_zero 2 hc)]

theorem projectiveNaturalRootLine_eq_iff (r : ℕ) (hr : 0 < r)
    (v w : Index (r + 1) → K) (hv : v ≠ 0) :
    projectiveNaturalRootLine r hr v = projectiveNaturalRootLine r hr w ↔
      ∃ c : K, c ≠ 0 ∧ v = c • w := by
  constructor
  · intro he
    have hm : projectiveNaturalRootHom r hr v (Multiplicative.ofAdd 1) ∈
        projectiveNaturalRootLine r hr v := ⟨Multiplicative.ofAdd 1, rfl⟩
    rw [he] at hm
    obtain ⟨a, ha⟩ := hm
    have hLift := actualNaturalRootElement_eq_of_projective_eq r hr v w 1 a.toAdd ha.symm
    have hT : transvection (r + 1) v 1 = transvection (r + 1) w a.toAdd := by
      apply LinearEquiv.ext
      intro x
      have h := congrArg (fun g : elementaryRootGroup K (r + 1) => (g.val : Mat K (r + 1)) *ᵥ x) hLift
      simpa only [actualNaturalRootElement_apply] using h
    exact transvection_eq_imp_smul (r + 1) v w 1 a.toAdd hv one_ne_zero hT
  · rintro ⟨c, hc, hvc⟩
    rw [hvc]
    exact projectiveNaturalRootLine_smul r hr w c hc

theorem projectiveNaturalRootElement_conjugation (r : ℕ) (hr : 0 < r)
    (g : elementaryRootGroup K (r + 1)) (v : Index (r + 1) → K) (a : K) :
    let q := QuotientGroup.mk' (Subgroup.center (elementaryRootGroup K (r + 1)))
    q g * projectiveNaturalRootHom r hr v (Multiplicative.ofAdd a) * (q g)⁻¹ =
      projectiveNaturalRootHom r hr ((g.val : Mat K (r + 1)) *ᵥ v) (Multiplicative.ofAdd a) := by
  let q := QuotientGroup.mk' (Subgroup.center (elementaryRootGroup K (r + 1)))
  have h := congrArg q (actualNaturalRootElement_conjugation r hr g v a)
  simpa only [map_mul, map_inv] using h

end SymmetricSubgroupAsymptotics.CFSGSymplecticTransvectionGeometry
