import SymmetricSubgroupAsymptotics.CFSGTwistedA2TorusAction

/-! Explicit inverse parameters for the torus commutator map on the
actual norm-constrained two-step unipotent law. No Lang theorem or
source-derived-membership premise is assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGTwistedA2UnipotentArrays
variable {K : Type} [Field K] (σ : K ≃+* K)

theorem commutatorParameters_surjective (hσ : Function.Involutive σ)
    (k n : K) (hkn : k * σ k = n) (hnfix : σ n = n)
    (hk : k ≠ 1) (hn : n ≠ 1) (A B : K) (hAB : NormCondition σ A B) :
    ∃ a b : K, NormCondition σ a b ∧
      (k - 1) * a = A ∧ (n - 1) * b + (1 - k) * a * σ a = B := by
  let a := A / (k - 1)
  let b := (B + (k - 1) * a * σ a) / (n - 1)
  have hk0 : k - 1 ≠ 0 := sub_ne_zero.mpr hk
  have hn0 : n - 1 ≠ 0 := sub_ne_zero.mpr hn
  have hA : (k - 1) * a = A := by dsimp only [a]; field_simp [hk0]
  have hAs : (σ k - 1) * σ a = σ A := by
    have h := congrArg σ hA
    simpa only [map_mul, map_sub, map_one] using h
  have hnorm : A * σ A = (n - k - σ k + 1) * a * σ a := by
    calc
      _ = ((k - 1) * a) * ((σ k - 1) * σ a) :=
        congrArg₂ (· * ·) hA.symm hAs.symm
      _ = _ := by rw [← hkn]; ring
  have hden : σ (n - 1) = n - 1 := by rw [map_sub, map_one, hnfix]
  have hnum : (B + (k - 1) * a * σ a) + σ (B + (k - 1) * a * σ a) =
      (n - 1) * a * σ a := by
    calc
      _ = (B + σ B) + (k + σ k - 2) * a * σ a := by
        simp only [map_add, map_mul, map_sub, map_one, hσ a]
        ring
      _ = A * σ A + (k + σ k - 2) * a * σ a := by rw [hAB]
      _ = _ := by rw [hnorm]; ring
  refine ⟨a, b, ?_, hA, ?_⟩
  · change b + σ b = a * σ a
    have hb : σ b = σ (B + (k - 1) * a * σ a) / (n - 1) := by
      change σ ((B + (k - 1) * a * σ a) / (n - 1)) = _
      exact (map_div₀ σ (B + (k - 1) * a * σ a) (n - 1)).trans
        (congrArg (fun d : K => σ (B + (k - 1) * a * σ a) / d) hden)
    rw [hb]
    change (B + (k - 1) * a * σ a) / (n - 1) +
      σ (B + (k - 1) * a * σ a) / (n - 1) = _
    rw [← add_div, hnum]
    field_simp [hn0]
  · dsimp only [b]
    field_simp [hn0]
    ring

end SymmetricSubgroupAsymptotics.CFSGTwistedA2UnipotentArrays
