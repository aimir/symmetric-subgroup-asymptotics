import SymmetricSubgroupAsymptotics.MarkedC4CoprimePhysicalGrid

/-! Explicit representative formulas and equivariance of the constructed
physical grid. These are the recovery link to the original action. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.MarkedC4.CoprimeGridEquivariance
variable {P O X : Type} [Group P] [Group O] [Finite P] [Finite O]
  [MulAction (P × O) X] (hcop : Nat.Coprime (Nat.card P) (Nat.card O))

private theorem quotient_cast_mk {G : Type} [Group G] {K L : Subgroup G}
    (h : K=L) (g : G) :
    Equiv.cast (congrArg (fun H : Subgroup G => G ⧸ H) h)
      (QuotientGroup.mk g) = QuotientGroup.mk g := by
  cases h
  rfl

/-- Grid coordinates of an ACTUAL original orbit point. -/
theorem grid_apply (x : X) (p : P) (o : O) :
    CoprimePhysicalGrid.orbitGrid hcop x
      ⟨(p,o) • x,MulAction.mem_orbit x (p,o)⟩ =
      (QuotientGroup.mk p,QuotientGroup.mk o) := by
  let e := MulAction.orbitEquivQuotientStabilizer (P × O) x
  have hs : e.symm (QuotientGroup.mk (p,o))=
      ⟨(p,o) • x,MulAction.mem_orbit x (p,o)⟩ := by
    apply Subtype.ext
    exact MulAction.orbitEquivQuotientStabilizer_symm_apply (P × O) x (p,o)
  have he : e ⟨(p,o) • x,MulAction.mem_orbit x (p,o)⟩=QuotientGroup.mk (p,o) := by
    rw [← hs,e.apply_symm_apply]
  unfold CoprimePhysicalGrid.orbitGrid
  change QuotientGroup.prodEquiv _ _
    (Equiv.cast (congrArg (fun K : Subgroup (P × O) => (P × O) ⧸ K)
      (CoprimePhysicalGrid.subgroup_eq_product hcop (MulAction.stabilizer (P × O) x)))
      (e ⟨(p,o) • x,MulAction.mem_orbit x (p,o)⟩))=_
  rw [he]
  rw [quotient_cast_mk (CoprimePhysicalGrid.subgroup_eq_product hcop
    (MulAction.stabilizer (P × O) x)) (p,o)]
  rfl

/-- The grid intertwines the original product action with the two
coordinate coset actions; no equivariance premise has been added. -/
theorem grid_equivariant (x : X) (g : P × O) (z : MulAction.orbit (P × O) x) :
    CoprimePhysicalGrid.orbitGrid hcop x (g • z)=
      (g.1 • (CoprimePhysicalGrid.orbitGrid hcop x z).1,
       g.2 • (CoprimePhysicalGrid.orbitGrid hcop x z).2) := by
  rcases z with ⟨z,hz⟩
  obtain ⟨⟨p,o⟩,rfl⟩ := hz
  have hpoint : g • (⟨(p,o) • x,MulAction.mem_orbit x (p,o)⟩ :
      MulAction.orbit (P × O) x)=
      ⟨(g.1*p,g.2*o) • x,MulAction.mem_orbit x (g.1*p,g.2*o)⟩ := by
    apply Subtype.ext
    exact (mul_smul g (p,o) x).symm
  rw [hpoint,grid_apply,grid_apply]
  rfl
end SymmetricSubgroupAsymptotics.MarkedC4.CoprimeGridEquivariance
