import SymmetricSubgroupAsymptotics.BinaryPairFrameFourMonolith

/-! Bind a selected actual central-quotient graph to the structural normal
cover. The literal kernel test is only identity versus the original
constant flip; it does not enumerate ambient normal subgroups. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryPairFrame

variable {X H : Type} [Group H] {U : Subgroup (Equiv.Perm X)}
    (F : BinaryPairFrame U (Fin 4))

/-- The selected graph's pointwise two-element kernel test supplies both
first-stage retained-chain obligations, on the original group and normals.
The eventual retained axis above this central kernel is deliberately not
identified with the pair kernel. -/
theorem centralQuotient_normalCover
    (P : Subgroup F.top.range) [P.Normal] (hP : IsPGroup 2 P)
    (u v : P)
    (hu : ∀ x i, F.coordinateTopAction u x i = x (![1, 0, 3, 2] i))
    (hv : ∀ x i, F.coordinateTopAction v x i = x (![2, 3, 0, 1] i))
    (c : F.top.ker) (hc : ∀ i, F.bits c i = 1)
    (hsep : ∀ i j : Fin 4, i ≠ j →
      ∃ k : F.top.ker, F.bits k i ≠ F.bits k j)
    (q : U →* H) (hker : ∀ g : U, q g = 1 ↔ g = 1 ∨ g = (c : U)) :
    q.ker ≠ ⊥ ∧
      ∀ N : Subgroup U, N.Normal → N ≠ ⊥ → q.ker ≤ N := by
  have hcne : (c : U) ≠ 1 := by
    intro he
    have hec : c = 1 := Subtype.ext he
    have h := congrArg (fun a : Multiplicative (Fin 4 → ZMod 2) => a.toAdd 0)
      F.bitsHom.map_one
    change F.bits 1 0 = 0 at h
    rw [← hec, hc] at h
    exact one_ne_zero h
  constructor
  · intro hbot
    have hm : (c : U) ∈ q.ker := (hker (c : U)).mpr (Or.inr rfl)
    rw [hbot] at hm
    exact hcne (Subgroup.mem_bot.mp hm)
  · intro N hN hne g hg
    rcases (hker g).mp hg with hgone | hgc
    · simpa only [hgone] using N.one_mem
    · rw [hgc]
      exact F.constantFlip_mem_every_nontrivial_normal P hP u v hu hv c hc hsep N hN hne

end SymmetricSubgroupAsymptotics.BinaryPairFrame

end
