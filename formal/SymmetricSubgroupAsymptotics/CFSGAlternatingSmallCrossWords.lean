import SymmetricSubgroupAsymptotics.CFSGAlternatingSmallCrossSeed

/-! Literal words for the degree-seven/eight seed. The product p*b is
the double transposition (0 4)(A B). Its rotation conjugate has the same
outside swap, which cancels to give the adjacent cycle on (4,0,1). -/
set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.CFSGAlternatingSmallCrossWords
open CFSGAlternatingCyclicReflection CFSGAlternatingSumSupport
open CFSGAlternatingCrossSeed CFSGPermutationCrossSwapWords
open CFSGAlternatingSmallCrossSeed

theorem extension_swap (r : ℕ) (u v : Cycle 1) :
    extensionHom (Cycle 1) r (Equiv.swap u v) = Equiv.swap (Sum.inl u) (Sum.inl v) := by
  apply Equiv.ext
  intro x
  cases x with
  | inl x =>
      by_cases hx : x = u
      · subst x; simp [Equiv.swap_apply_def]
      by_cases hv : x = v
      · subst x; simp [Equiv.swap_apply_def, hx]
      simp [Equiv.swap_apply_def, hx, hv]
  | inr i => simp [Equiv.swap_apply_def]

def a (r : ℕ) (hr : 2 ≤ r) : Equiv.Perm (X 1 r) :=
  doubleSwap (Sum.inl 0) (Sum.inl 4)
    (Sum.inr ⟨0, by omega⟩) (Sum.inr ⟨1, by omega⟩)

theorem baseReflection_matching : baseReflection = doubleSwap (0 : Cycle 1) 4 1 3 := by
  decide +kernel

theorem p_mul_b (r : ℕ) (hr : 2 ≤ r) :
    CFSGAlternatingSmallCrossSeed.p r * b r hr = a r hr := by
  change extensionHom (Cycle 1) r baseReflection *
    doubleSwap (Sum.inl 1) (Sum.inl 3) (Sum.inr ⟨0, by omega⟩) (Sum.inr ⟨1, by omega⟩) = _
  rw [baseReflection_matching]
  simp only [doubleSwap, map_mul, extension_swap]
  change (Equiv.swap (Sum.inl (0 : Cycle 1)) (Sum.inl 4) * Equiv.swap (Sum.inl 1) (Sum.inl 3)) *
    (Equiv.swap (Sum.inl 1) (Sum.inl 3) * Equiv.swap (Sum.inr (⟨0, by omega⟩ : Fin r))
      (Sum.inr ⟨1, by omega⟩)) = _
  rw [mul_assoc, ← mul_assoc (Equiv.swap (Sum.inl (1 : Cycle 1)) (Sum.inl 3)),
    Equiv.swap_mul_self, one_mul]
  rfl

theorem conjugate_a (r : ℕ) (hr : 2 ≤ r) :
    g 1 r * a r hr * (g 1 r)⁻¹ =
      doubleSwap (Sum.inl 1) (Sum.inl 0)
        (Sum.inr (⟨0, by omega⟩ : Fin r)) (Sum.inr ⟨1, by omega⟩) := by
  rw [a, CFSGAlternatingDoubleSwapGeneration.conjugate_doubleSwap]
  have h0 : g 1 r (Sum.inl 0) = Sum.inl 1 := by
    change Sum.inl ((0 : Cycle 1) + 1) = Sum.inl 1
    simp
  have h4 : g 1 r (Sum.inl 4) = Sum.inl 0 := by
    exact congrArg (fun x : Cycle 1 => (Sum.inl x : X 1 r))
      (by decide +kernel : (4 : Cycle 1) + 1 = 0)
  rw [h0, h4]
  rfl

theorem adjacent_word (r : ℕ) (hr : 2 ≤ r) :
    a r hr * (g 1 r * a r hr * (g 1 r)⁻¹) =
      extensionHom (Cycle 1) r (Equiv.swap (4 : Cycle 1) 0 * Equiv.swap 0 1) := by
  rw [conjugate_a]
  have hd : [Sum.inr (⟨0, by omega⟩ : Fin r), Sum.inr ⟨1, by omega⟩,
      Sum.inl (1 : Cycle 1), Sum.inl 0].Nodup := by
    simp [Fin.ext_iff, show (1 : Cycle 1) ≠ 0 by decide]
  have hc := (Equiv.Perm.disjoint_swap_swap hd).commute
  let s : Equiv.Perm (X 1 r) :=
    Equiv.swap (Sum.inr (⟨0, by omega⟩ : Fin r)) (Sum.inr ⟨1, by omega⟩)
  have hs : s * s = 1 := Equiv.swap_mul_self _ _
  change (Equiv.swap (Sum.inl (0 : Cycle 1)) (Sum.inl 4) * s) *
      (Equiv.swap (Sum.inl 1) (Sum.inl 0) * s) = _
  calc
    _ = Equiv.swap (Sum.inl (0 : Cycle 1)) (Sum.inl 4) *
        ((s * Equiv.swap (Sum.inl 1) (Sum.inl 0)) * s) := by group
    _ = Equiv.swap (Sum.inl (0 : Cycle 1)) (Sum.inl 4) *
        ((Equiv.swap (Sum.inl 1) (Sum.inl 0) * s) * s) := by rw [hc.eq]
    _ = Equiv.swap (Sum.inl (0 : Cycle 1)) (Sum.inl 4) * Equiv.swap (Sum.inl 1) (Sum.inl 0) := by
      rw [mul_assoc, hs]
      exact congrArg (fun z : Equiv.Perm (X 1 r) => Equiv.swap (Sum.inl (0 : Cycle 1)) (Sum.inl 4) * z)
        (mul_one (Equiv.swap (Sum.inl (1 : Cycle 1)) (Sum.inl 0)))
    _ = _ := by
      rw [map_mul, extension_swap, extension_swap,
        Equiv.swap_comm (Sum.inl (4 : Cycle 1)) (Sum.inl 0),
        Equiv.swap_comm (Sum.inl (0 : Cycle 1)) (Sum.inl 1)]

end SymmetricSubgroupAsymptotics.CFSGAlternatingSmallCrossWords
