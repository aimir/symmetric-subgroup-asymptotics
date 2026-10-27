import SymmetricSubgroupAsymptotics.FiniteExtensionSelfNormalizingKernelLift

/-! Transport the self-normalizing full-subdirect theorem through the
actual ambient kernel chart. The conclusion concerns every complete lift
of that same K, not just its normalizer or an abstract extension type. -/
set_option autoImplicit false
namespace SymmetricSubgroupAsymptotics.ActualSimplePowerKernelUniqueLift

variable {E Q T : Type} [Group E] [Group Q] [Group T] [Finite T] [IsSimpleGroup T]

theorem self_normalizing_inside_kernel (π : E →* Q) (K : Subgroup E)
    (n : ℕ) (e : π.ker ≃* (Fin n → T)) (hZ : IsCenterless T)
    (hfull : ∀ i : Fin n,Function.Surjective
      (fun k : (K.subgroupOf π.ker).map e.toMonoidHom => k.val i)) :
    ∀ g : E,g∈π.ker → g∈Subgroup.normalizer (K : Set E) → g∈K := by
  intro g hg hgn
  let v : π.ker := ⟨g,hg⟩
  have hvN : v∈Subgroup.normalizer (K.subgroupOf π.ker : Set π.ker) := by
    apply Subgroup.mem_normalizer_iff.mpr
    intro x
    change x.val∈K ↔ g*x.val*g⁻¹∈K
    exact Subgroup.mem_normalizer_iff.mp hgn x.val
  have hm := Subgroup.le_normalizer_map e.toMonoidHom ⟨v,hvN,rfl⟩
  have hn := SimplePowerSubdirectSelfNormalizer.normalizer_eq T hZ n
    ((K.subgroupOf π.ker).map e.toMonoidHom) hfull
  rw [hn] at hm
  obtain ⟨w,hw,he⟩ := hm
  have hwv : w=v := e.injective he
  have hv : v∈K.subgroupOf π.ker := hwv ▸ hw
  exact hv

theorem subsingleton_fullImage_fixedKernel (π : E →* Q) (K : Subgroup E)
    (n : ℕ) (e : π.ker ≃* (Fin n → T)) (hZ : IsCenterless T)
    (hfull : ∀ i : Fin n,Function.Surjective
      (fun k : (K.subgroupOf π.ker).map e.toMonoidHom => k.val i)) :
    Subsingleton {L : Subgroup E // L.map π=⊤ ∧ L⊓π.ker=K} :=
  FiniteExtensionSelfNormalizingKernelLift.subsingleton_fullImage_fixedKernel π K
    (self_normalizing_inside_kernel π K n e hZ hfull)

end SymmetricSubgroupAsymptotics.ActualSimplePowerKernelUniqueLift
