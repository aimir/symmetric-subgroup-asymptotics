import SymmetricSubgroupAsymptotics.CFSGOrthogonalBGenerationInitialTorusAction
import SymmetricSubgroupAsymptotics.CFSGOrthogonalBElementaryCenter
import SymmetricSubgroupAsymptotics.CFSGConjugateSubgroupDegree
import SymmetricSubgroupAsymptotics.CFSGOrthogonalBProjectiveRealization

/-! The original terminal short-root group injects into the actual odd
B central quotient. Its nonidentity elements are conjugate by the SAME
actual torus words, so every proper coset action has degree at least q. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalBIndexRootSubgroup
open CFSGOrthogonalBSerreMatrices CFSGOrthogonalBGenerationInitialElements
open CFSGOrthogonalBGenerationElements CFSGOrthogonalBGenerationShortArrays
open CFSGOrthogonalBGenerationInitialTorusAction
variable (K : Type) [Field K]

def terminalHom (s : ℕ) : Multiplicative K →* elementaryRootGroup K (s + 3) where
  toFun a := betaElement K s a.toAdd
  map_one' := rootElement_zero K (s + 3) false (lastIndex s)
  map_mul' a b := rootElement_add K (s + 3) false (lastIndex s) a.toAdd b.toAdd

def projectiveTerminalHom (s : ℕ) : Multiplicative K →* elementaryProjective K (s + 3) :=
  (QuotientGroup.mk' (Subgroup.center (elementaryRootGroup K (s + 3)))).comp (terminalHom K s)

theorem terminal_parameter_zero_of_central (h2 : (2 : K) ≠ 0) (s : ℕ) (a : K)
    (ha : betaElement K s a ∈ Subgroup.center (elementaryRootGroup K (s + 3))) : a = 0 := by
  obtain ⟨c, hc⟩ := (elementaryRootGroup_center_iff_scalar K (s + 2) h2
    (betaElement K s a)).mp ha
  have he := congrArg (fun M : Mat K (s + 3) =>
    M (pos (s + 3) (lastIndex s)) (middle (s + 3))) hc
  simpa [betaElement_val, betaUnit, shortUnit_val, shortArray, shortSecond,
    pos, neg, middle, paired, Matrix.single_apply, Matrix.one_apply] using he

theorem projectiveTerminalHom_injective (h2 : (2 : K) ≠ 0) (s : ℕ) :
    Function.Injective (projectiveTerminalHom K s) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply bot_unique
  intro a ha
  have hc : betaElement K s a.toAdd ∈ Subgroup.center (elementaryRootGroup K (s + 3)) :=
    (QuotientGroup.eq_one_iff _).mp ha
  have hz := terminal_parameter_zero_of_central K h2 s a.toAdd hc
  exact Subgroup.mem_bot.mpr (congrArg Multiplicative.ofAdd hz)

def projectiveTerminalRoot (s : ℕ) : Subgroup (elementaryProjective K (s + 3)) :=
  (projectiveTerminalHom K s).range

theorem projectiveTerminalRoot_card (h2 : (2 : K) ≠ 0) (s : ℕ) :
    Nat.card (projectiveTerminalRoot K s) = Nat.card K := by
  calc
    Nat.card (projectiveTerminalRoot K s) = Nat.card (Multiplicative K) :=
      Nat.card_congr (MonoidHom.ofInjective (projectiveTerminalHom_injective K h2 s)).symm.toEquiv
    _ = Nat.card K := Nat.card_congr Multiplicative.toAdd

theorem projectiveTerminal_nonidentity_conjugate (h2 : (2 : K) ≠ 0) (s : ℕ)
    (a b : projectiveTerminalRoot K s) (ha : a ≠ 1) (hb : b ≠ 1) :
    ∃ z : elementaryProjective K (s + 3), z * a.val * z⁻¹ = b.val := by
  obtain ⟨u, hu⟩ := a.property
  obtain ⟨v, hv⟩ := b.property
  have hu0 : u.toAdd ≠ 0 := by
    intro hz
    apply ha
    apply Subtype.ext
    rw [← hu, show u = 1 from congrArg Multiplicative.ofAdd hz, map_one]
    rfl
  have hv0 : v.toAdd ≠ 0 := by
    intro hz
    apply hb
    apply Subtype.ext
    rw [← hv, show v = 1 from congrArg Multiplicative.ofAdd hz, map_one]
    rfl
  let g : Kˣ := Units.mk0 (v.toAdd / u.toAdd) (div_ne_zero hv0 hu0)
  have hg : (g : K) * u.toAdd = v.toAdd := div_mul_cancel₀ _ hu0
  let q := QuotientGroup.mk' (Subgroup.center (elementaryRootGroup K (s + 3)))
  refine ⟨q (initialTorus K h2 s g), ?_⟩
  rw [← hu, ← hv]
  have he : initialTorus K h2 s g * betaElement K s u.toAdd *
      (initialTorus K h2 s g)⁻¹ = betaElement K s v.toAdd := by
    apply Subtype.ext
    change (initialTorus K h2 s g).val * (betaElement K s u.toAdd).val *
      (initialTorus K h2 s g).val⁻¹ = (betaElement K s v.toAdd).val
    rw [betaElement_val, betaElement_val, initialTorus_beta, hg]
  exact congrArg q he

theorem field_card_le_proper_index [Finite K] (h2 : (2 : K) ≠ 0) (s : ℕ)
    [IsSimpleGroup (elementaryProjective K (s + 3))]
    (H : Subgroup (elementaryProjective K (s + 3))) (hH : H ≠ ⊤) : Nat.card K ≤ H.index := by
  letI oddBIndex_projectiveFinite : Finite (elementaryProjective K (s + 3)) :=
    Finite.of_surjective
      (QuotientGroup.mk' (Subgroup.center (elementaryRootGroup K (s + 3))))
      (QuotientGroup.mk'_surjective _)
  let f := projectiveTerminalHom K s
  have hne : f (Multiplicative.ofAdd (1 : K)) ≠ 1 := by
    intro h
    have hh := projectiveTerminalHom_injective K h2 s (h.trans f.map_one.symm)
    exact one_ne_zero (congrArg Multiplicative.toAdd hh)
  let a : projectiveTerminalRoot K s := ⟨f (Multiplicative.ofAdd (1 : K)), ⟨_, rfl⟩⟩
  have ha : a ≠ 1 := fun h => hne (congrArg Subtype.val h)
  letI oddBIndex_rootNontrivial : Nontrivial (projectiveTerminalRoot K s) := ⟨⟨a, 1, ha⟩⟩
  have hh := CFSGConjugateSubgroupDegree.card_le_index_of_nonidentity_conjugate
    (projectiveTerminalRoot K s) (projectiveTerminal_nonidentity_conjugate K h2 s) H hH
  rwa [projectiveTerminalRoot_card K h2 s] at hh

end SymmetricSubgroupAsymptotics.CFSGOrthogonalBIndexRootSubgroup
