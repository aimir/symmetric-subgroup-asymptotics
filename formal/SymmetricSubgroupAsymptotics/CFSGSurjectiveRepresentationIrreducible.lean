import SymmetricSubgroupAsymptotics.PrimitiveAffineBottomFibre

/-! A surjective equivariant linear map transports irreducibility even when
the acting group changes through a specified homomorphism. The zero target
is separated explicitly; no semisimplicity or characteristic assumption is
used. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics

variable {k G H V W : Type} [Field k] [Group G] [Group H]
    [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]

theorem representationIrreducible_of_surjective_equivariant
    (rho : Representation k G V) (tau : Representation k H W)
    (phi : G →* H) (f : V →ₗ[k] W) (hf : Function.Surjective f)
    (he : ∀ g v, f (rho g v) = tau (phi g) (f v))
    (hirr : Representation.IsIrreducible rho) [Nontrivial W] :
    Representation.IsIrreducible tau := by
  have hbt : (⊥ : Subrepresentation tau) ≠ ⊤ := by
    obtain ⟨w,hw⟩ := exists_ne (0 : W)
    intro hh
    have hm : w ∈ (⊥ : Subrepresentation tau) := by rw [hh]; trivial
    exact hw ((Submodule.mem_bot (R := k)).mp hm)
  letI : Nontrivial (Subrepresentation tau) := ⟨⟨⊥,⊤,hbt⟩⟩
  refine { eq_bot_or_eq_top := ?_ }
  intro S
  let T : Subrepresentation rho :=
    { toSubmodule := S.toSubmodule.comap f
      apply_mem_toSubmodule := by
        intro g v hv
        change f (rho g v) ∈ S
        rw [he]
        exact S.apply_mem_toSubmodule (phi g) hv }
  rcases hirr.eq_bot_or_eq_top T with hT | hT
  · left
    apply Subrepresentation.toSubmodule_injective
    apply SetLike.ext
    intro w
    constructor
    · intro hw
      obtain ⟨v,rfl⟩ := hf w
      have hv : v ∈ T := hw
      rw [hT] at hv
      have hv0 : v = 0 := (Submodule.mem_bot (R := k)).mp hv
      simp [hv0]
    · intro hw
      have hw0 : w = 0 := (Submodule.mem_bot (R := k)).mp hw
      rw [hw0]
      exact Submodule.zero_mem _
  · right
    apply Subrepresentation.toSubmodule_injective
    apply SetLike.ext
    intro w
    constructor
    · intro _
      exact Submodule.mem_top
    · intro _
      obtain ⟨v,rfl⟩ := hf w
      have hv : v ∈ T := by rw [hT]; trivial
      exact hv

end SymmetricSubgroupAsymptotics
