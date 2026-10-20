import SymmetricSubgroupAsymptotics.InducedSylowMiddleGenerators
import SymmetricSubgroupAsymptotics.PrimeGridMiddleCapacity

/-! The least actual uniform tuple length simultaneously inherits every
proved route to a generating capacity. No numerical conclusion is assumed. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical BigOperators
namespace SymmetricSubgroupAsymptotics.InducedMinimumUniformCapacity

variable {p : ℕ} [Fact p.Prime] {G V : Type} [Group G] [Finite G]
    [AddCommGroup V] [Module (ZMod p) V] [FiniteDimensional (ZMod p) V]
    (H : Subgroup G) (rho : Representation (ZMod p) H V)

private theorem exists_uniform : ∃ n : ℕ,
    UniformSubrepresentationGeneratorBound (Representation.ind H.subtype rho) n := by
  let P : Sylow p G := Classical.choice inferInstance
  letI : Finite (DoubleCoset.Quotient (H : Set G) ((P : Subgroup G) : Set G)) :=
    Finite.of_injective (inducedDoubleCosetOrbitEquiv H (P : Subgroup G))
      (inducedDoubleCosetOrbitEquiv H (P : Subgroup G)).injective
  letI : Fintype (DoubleCoset.Quotient (H : Set G) ((P : Subgroup G) : Set G)) := Fintype.ofFinite _
  obtain ⟨j,hj,_,_⟩ := inducedMackeySylow_indices H p P
  exact ⟨_,induced_sylow_middle_uniform H P rho j hj⟩

def capacity : ℕ := Nat.find (exists_uniform H rho)

theorem uniform : UniformSubrepresentationGeneratorBound
    (Representation.ind H.subtype rho) (capacity H rho) := Nat.find_spec (exists_uniform H rho)

theorem le_of_uniform {n : ℕ}
    (hn : UniformSubrepresentationGeneratorBound (Representation.ind H.subtype rho) n) :
    capacity H rho≤n := Nat.find_min' (exists_uniform H rho) hn

/-- Every actual defining-characteristic Sylow width sum bounds the same
least uniform integer. The displayed local inequality is supplied by the
proved actual prime-grid count. -/
theorem le_of_sylow_middle (P : Sylow p G)
    [Fintype (DoubleCoset.Quotient (H : Set G) ((P : Subgroup G) : Set G))]
    (j : DoubleCoset.Quotient (H : Set G) ((P : Subgroup G) : Set G) → ℕ)
    (hj : ∀ q,(inducedOrbitStabilizer H (P : Subgroup G) q.out).index=p^j q)
    (hs : ∑ q,p^j q=H.index) (C : ℝ)
    (hC : ∀ q,(primeGridMiddleWidth p (j q) : ℝ)≤(p : ℝ)^j q*C) :
    (capacity H rho : ℝ)≤(Module.finrank (ZMod p) V : ℝ)*H.index*C := by
  have hn := le_of_uniform H rho (induced_sylow_middle_uniform H P rho j hj)
  have hnc : (capacity H rho : ℝ)≤
      ((∑ q,Module.finrank (ZMod p) V*primeGridMiddleWidth p (j q) : ℕ) : ℝ) := by
    exact_mod_cast hn
  have hsR : (∑ q,(p : ℝ)^j q)=(H.index : ℝ) := by exact_mod_cast hs
  apply hnc.trans
  calc
    ((∑ q,Module.finrank (ZMod p) V*primeGridMiddleWidth p (j q) : ℕ) : ℝ)=
        ∑ q,(Module.finrank (ZMod p) V : ℝ)*(primeGridMiddleWidth p (j q) : ℝ) := by simp
    _ ≤ ∑ q,(Module.finrank (ZMod p) V : ℝ)*((p : ℝ)^j q*C) :=
      Finset.sum_le_sum (fun q _ => mul_le_mul_of_nonneg_left (hC q) (by positivity))
    _ = (Module.finrank (ZMod p) V : ℝ)*(∑ q,(p : ℝ)^j q)*C := by
      simp only [Finset.mul_sum,Finset.sum_mul,mul_assoc]
    _ = (Module.finrank (ZMod p) V : ℝ)*H.index*C := by rw [hsR]

/-- The exact primary square-root field, with the original local fibre,
subgroup, and least actual generator count retained. -/
theorem primary (e : ℕ) (he : 1≤e) (hdiv : p^e∣H.index) :
    (capacity H rho : ℝ)≤(Module.finrank (ZMod p) V : ℝ)*H.index*
      Real.sqrt (2/(3*((p : ℝ)-1)*e)) := by
  let P : Sylow p G := Classical.choice inferInstance
  letI : Finite (DoubleCoset.Quotient (H : Set G) ((P : Subgroup G) : Set G)) :=
    Finite.of_injective (inducedDoubleCosetOrbitEquiv H (P : Subgroup G))
      (inducedDoubleCosetOrbitEquiv H (P : Subgroup G)).injective
  letI : Fintype (DoubleCoset.Quotient (H : Set G) ((P : Subgroup G) : Set G)) := Fintype.ofFinite _
  obtain ⟨j,hj,hval,hs⟩ := inducedMackeySylow_indices H p P
  apply le_of_sylow_middle H rho P j hj hs
  intro q
  have heval : e≤H.index.factorization p :=
    ((Fact.out : p.Prime).pow_dvd_iff_le_factorization H.index_ne_zero_of_finite).mp hdiv
  exact primeGridMiddleWidth_primary p (j q) e (Fact.out : p.Prime).two_le he
    (heval.trans (hval q))

end SymmetricSubgroupAsymptotics.InducedMinimumUniformCapacity
