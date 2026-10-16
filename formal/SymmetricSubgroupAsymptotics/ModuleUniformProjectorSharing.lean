import SymmetricSubgroupAsymptotics.ModuleGeneratorProjectionSharing

/-! Uniform generator sharing for two actual projector components. -/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics.ModuleGeneratedBy

variable {R M : Type} [Ring R] [AddCommGroup M] [Module R M]

theorem uniform_of_projector
    (A B : Submodule R M) (r : R) (n : ℕ)
    (hrA : ∀ a : A, r • (a : M) = a)
    (hrB : ∀ b : B, r • (b : M) = 0)
    (hprojA : ∀ x : M, r • x ∈ A)
    (hprojB : ∀ x : M, x - r • x ∈ B)
    (hA : ∀ U : Submodule R M, U ≤ A → ModuleGeneratedBy R U n)
    (hB : ∀ U : Submodule R M, U ≤ B → ModuleGeneratedBy R U n)
    (W : Submodule R M) : ModuleGeneratedBy R W n := by
  let P : Submodule R W := A.comap W.subtype
  let Q : Submodule R W := B.comap W.subtype
  have hPmap : P.map W.subtype ≤ A := by
    rintro _ ⟨x, hx, rfl⟩
    exact hx
  have hQmap : Q.map W.subtype ≤ B := by
    rintro _ ⟨x, hx, rfl⟩
    exact hx
  have hgenP : ModuleGeneratedBy R P n :=
    congr (Submodule.equivMapOfInjective W.subtype W.subtype_injective P).symm
      (hA _ hPmap)
  have hgenQ : ModuleGeneratedBy R Q n :=
    congr (Submodule.equivMapOfInjective W.subtype W.subtype_injective Q).symm
      (hB _ hQmap)
  apply of_projected_submodules P Q r ?_ ?_ ?_ n hgenP hgenQ
  · intro x
    apply Subtype.ext
    exact hrA ⟨x.1.1, x.2⟩
  · intro x
    apply Subtype.ext
    exact hrB ⟨x.1.1, x.2⟩
  · apply top_unique
    intro x _
    let p : W := ⟨r • x.1, W.smul_mem r x.2⟩
    let q : W := x - p
    have hp : p ∈ P := hprojA x.1
    have hq : q ∈ Q := hprojB x.1
    have hsum : x = p + q := by
      apply Subtype.ext
      dsimp [p, q]
      abel
    rw [hsum]
    exact (P ⊔ Q).add_mem
      ((show P ≤ P ⊔ Q from le_sup_left) hp)
      ((show Q ≤ P ⊔ Q from le_sup_right) hq)

end SymmetricSubgroupAsymptotics.ModuleGeneratedBy

end
