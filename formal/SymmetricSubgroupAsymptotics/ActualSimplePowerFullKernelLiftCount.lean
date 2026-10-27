import SymmetricSubgroupAsymptotics.ActualSimplePowerKernelUniqueLift

/-! Count ALL complete full-image lifts whose actual kernel has full
simple coordinate projections. The kernel code is injective because its
full subdirect subgroup is self-normalizing in the actual ambient kernel.
No quotient-generator factor is charged in this sector. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.ActualSimplePowerFullKernelLiftCount

variable {E Q T : Type} [Group E] [Group Q] [Group T] [Finite T] [IsSimpleGroup T]
variable (π : E →* Q) (n : ℕ) (e : π.ker ≃* (Fin n → T))

abbrev Family := {L : Subgroup E // L.map π=⊤ ∧
  ∀ i : Fin n,Function.Surjective
    (fun k : ((L⊓π.ker).subgroupOf π.ker).map e.toMonoidHom => k.val i)}

def code (L : Family π n e) : SimplePowerFullSubdirectCount.Family T n :=
  ⟨((L.val⊓π.ker).subgroupOf π.ker).map e.toMonoidHom,L.property.2⟩

theorem code_injective (hZ : IsCenterless T) : Function.Injective (code π n e) := by
  intro L M h
  have hm := congrArg (fun U : SimplePowerFullSubdirectCount.Family T n => U.val) h
  have hk := Subgroup.map_injective e.injective hm
  have ha := congrArg (fun U : Subgroup π.ker => U.map π.ker.subtype) hk
  have hi : L.val⊓π.ker=M.val⊓π.ker := by
    simpa only [Subgroup.subgroupOf_map_subtype,inf_assoc,inf_idem] using ha
  have hs := ActualSimplePowerKernelUniqueLift.self_normalizing_inside_kernel
    π (L.val⊓π.ker) n e hZ L.property.2
  exact Subtype.ext (FiniteExtensionSelfNormalizingKernelLift.eq_of_self_normalizing_intersection
    π (L.val⊓π.ker) L.val M.val L.property.1 M.property.1 rfl hi.symm hs)

theorem card_family_le (hZ : IsCenterless T) :
    Nat.card (Family π n e)≤(2*(1+n*Nat.card (T ≃* T)))^n :=
  (Nat.card_le_card_of_injective (code π n e) (code_injective π n e hZ)).trans
    (SimplePowerFullSubdirectCount.card_family_le T hZ n)

end SymmetricSubgroupAsymptotics.ActualSimplePowerFullKernelLiftCount
