import SymmetricSubgroupAsymptotics.SixPairBinaryQuotientCard
import SymmetricSubgroupAsymptotics.BinaryPairFrameTransport

/-! User-facing endpoints on the original transitive point action.
Transitivity of its pair-label action is derived from the actual frame. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics
namespace BinaryPairFrame

variable {X : Type} [Finite X] {U : Subgroup (Equiv.Perm X)}
    [MulAction.IsPretransitive U X] (F : BinaryPairFrame U (Fin 6))

include F

/-- The source needs only its actual transitive action and actual frame. -/
theorem original_binary_quotient_card_le_thirtyTwo
    (N : Subgroup U) [N.Normal] (hQ : IsPGroup 2 (U ⧸ N)) :
    Nat.card (U ⧸ N) ≤ 32 := by
  letI : MulAction U (Fin 6) := MulAction.compHom (Fin 6) F.top
  letI : MulAction.IsPretransitive U (Fin 6) := ⟨by
    intro i j
    obtain ⟨u,hu⟩ := MulAction.exists_smul_eq U (F.frame (i,0)) (F.frame (j,0))
    refine ⟨u,?_⟩
    change F.top u i = j
    have hi := F.intertwine u (i,0)
    change (F.frame.symm (u • F.frame (i,0))).1 = F.top u i at hi
    rw [hu,Equiv.symm_apply_apply] at hi
    exact hi.symm⟩
  exact F.binary_quotient_card_le_thirtyTwo (fun _ _ => rfl) N hQ

/-- Every binary image retains its actual epimorphism and kernel. -/
theorem original_binary_epimorphism_card_le_thirtyTwo
    {B : Type} [Group B] (f : U →* B) (hf : Function.Surjective f)
    (hB : IsPGroup 2 B) : Nat.card B ≤ 32 := by
  letI : Finite B := Finite.of_surjective f hf
  let e := QuotientGroup.quotientKerEquivOfSurjective f hf
  have hQ : IsPGroup 2 (U ⧸ f.ker) := hB.of_equiv e.symm
  rw [← Nat.card_congr e.toEquiv]
  exact F.original_binary_quotient_card_le_thirtyTwo f.ker hQ

/-- All Type-B cells are automatic, without a normal-state census. -/
def original_binary_quotient_B6_certificate
    (N : Subgroup U) [N.Normal] (hQ : IsPGroup 2 (U ⧸ N)) :
    PreE7B6QuotientCertificate (U ⧸ N) :=
  .binary hQ (F.original_binary_quotient_card_le_thirtyTwo N hQ)

end BinaryPairFrame
end SymmetricSubgroupAsymptotics
end
