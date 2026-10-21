import SymmetricSubgroupAsymptotics.MarkedC4CoprimeGridEquivariance

/-! The factors of a faithful transitive coprime product act faithfully
on their ACTUAL stabilizer-coset fibres. Thus a physical Sylow-grid factor
retains the action needed by the proved permutation rank/order estimates. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGCoprimeTransitiveFactorActions
open MarkedC4
variable {P O X : Type} [Group P] [Group O] [Finite P] [Finite O]
    [MulAction (P × O) X] [FaithfulSMul (P × O) X]
    [MulAction.IsPretransitive (P × O) X]
    (hcop : Nat.Coprime (Nat.card P) (Nat.card O)) (x : X)

abbrev LeftFiber := P ⧸ ((MulAction.stabilizer (P × O) x).map (MonoidHom.fst P O))
abbrev RightFiber := O ⧸ ((MulAction.stabilizer (P × O) x).map (MonoidHom.snd P O))

private theorem eq_of_eq_on_orbit (a b : P × O)
    (h : ∀ z : MulAction.orbit (P × O) x,a • z=b • z) : a=b := by
  apply eq_of_smul_eq_smul (α := X)
  intro y
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq (P × O) x y
  exact congrArg Subtype.val (h ⟨y,⟨g,hg⟩⟩)

include hcop

/-- No core-faithfulness premise is needed for the selected left fibre. -/
theorem left_faithful : FaithfulSMul P (LeftFiber (P := P) (O := O) x) := by
  constructor
  intro a b hab
  have he : ((a,1) : P × O)=(b,1) := by
    apply eq_of_eq_on_orbit x
    intro z
    apply (CoprimePhysicalGrid.orbitGrid hcop x).injective
    rw [CoprimeGridEquivariance.grid_equivariant,CoprimeGridEquivariance.grid_equivariant]
    apply Prod.ext
    · exact hab _
    · simp only [one_smul]
  exact congrArg Prod.fst he

/-- Both original factors are retained symmetrically. -/
theorem right_faithful : FaithfulSMul O (RightFiber (P := P) (O := O) x) := by
  constructor
  intro a b hab
  have he : ((1,a) : P × O)=(1,b) := by
    apply eq_of_eq_on_orbit x
    intro z
    apply (CoprimePhysicalGrid.orbitGrid hcop x).injective
    rw [CoprimeGridEquivariance.grid_equivariant,CoprimeGridEquivariance.grid_equivariant]
    apply Prod.ext
    · simp only [one_smul]
    · exact hab _
  exact congrArg Prod.snd he

/-- The factor degrees multiply to the original transitive degree. -/
theorem degree_product [Finite X] : Nat.card (LeftFiber (P := P) (O := O) x)*Nat.card (RightFiber (P := P) (O := O) x)=Nat.card X := by
  let e : MulAction.orbit (P × O) x ≃ X := Equiv.ofBijective Subtype.val
    ⟨Subtype.val_injective,fun y => by
      obtain ⟨g,hg⟩ := MulAction.exists_smul_eq (P × O) x y
      exact ⟨⟨y,⟨g,hg⟩⟩,rfl⟩⟩
  rw [←CoprimePhysicalGrid.orbit_card hcop x]
  exact Nat.card_congr e

end SymmetricSubgroupAsymptotics.CFSGCoprimeTransitiveFactorActions
