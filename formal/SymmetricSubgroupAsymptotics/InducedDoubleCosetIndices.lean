import SymmetricSubgroupAsymptotics.InducedOrbitStabilizer
import SymmetricSubgroupAsymptotics.TraceySylowIndices

/-! Literal Mackey double cosets are the actual restricted orbits on
the original coset action. Inversion fixes the orientation forced by
the coinduced function model. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics
variable {G : Type} [Group G] (H P : Subgroup G)

theorem inducedDoubleCoset_orbit_iff (x y : G) :
    MulAction.orbitRel P (G⧸H) ((x⁻¹:G):G⧸H) ((y⁻¹:G):G⧸H) ↔
      DoubleCoset.mk H P x=DoubleCoset.mk H P y := by
  rw [MulAction.orbitRel_apply,MulAction.mem_orbit_iff,DoubleCoset.eq]
  constructor
  · rintro ⟨p,hp⟩
    change (((p:G)*y⁻¹:G):G⧸H)=((x⁻¹:G):G⧸H) at hp
    have hh := QuotientGroup.eq.mp hp
    refine ⟨((p:G)*y⁻¹)⁻¹*x⁻¹,hh,p,p.2,?_⟩
    group
  · rintro ⟨h,hh,p,hp,hy⟩
    refine ⟨⟨p,hp⟩,?_⟩
    change ((p*y⁻¹:G):G⧸H)=((x⁻¹:G):G⧸H)
    apply QuotientGroup.eq.mpr
    have he : (p*y⁻¹)⁻¹*x⁻¹=h := by rw [hy]; group
    simpa only [he] using hh

def inducedDoubleCosetToOrbit :
    DoubleCoset.Quotient (H:Set G) (P:Set G) → MulAction.orbitRel.Quotient P (G⧸H) :=
  Quotient.lift (fun x : G => Quotient.mk'' ((x⁻¹:G):G⧸H)) (by
    intro x y h
    apply Quotient.sound
    exact (inducedDoubleCoset_orbit_iff H P x y).mpr (Quotient.sound h))

theorem inducedDoubleCosetToOrbit_injective : Function.Injective (inducedDoubleCosetToOrbit H P) := by
  intro a b
  refine Quotient.inductionOn₂ a b ?_
  intro x y h
  apply (inducedDoubleCoset_orbit_iff H P x y).mp
  exact Quotient.exact h

theorem inducedDoubleCosetToOrbit_surjective : Function.Surjective (inducedDoubleCosetToOrbit H P) := by
  intro a
  refine Quotient.inductionOn a ?_
  intro z
  refine Quotient.inductionOn z ?_
  intro g
  refine ⟨DoubleCoset.mk H P g⁻¹,?_⟩
  change Quotient.mk'' (((g⁻¹)⁻¹:G):G⧸H)=Quotient.mk'' (g:G⧸H)
  rw [inv_inv]

def inducedDoubleCosetOrbitEquiv :
    DoubleCoset.Quotient (H:Set G) (P:Set G) ≃ MulAction.orbitRel.Quotient P (G⧸H) :=
  Equiv.ofBijective (inducedDoubleCosetToOrbit H P)
    ⟨inducedDoubleCosetToOrbit_injective H P,inducedDoubleCosetToOrbit_surjective H P⟩

theorem inducedOrbitStabilizer_eq (x : G) :
    inducedOrbitStabilizer H P x=MulAction.stabilizer P ((x⁻¹:G):G⧸H) := by
  ext p
  change x*(p:G)*x⁻¹∈H ↔ p • ((x⁻¹:G):G⧸H)=((x⁻¹:G):G⧸H)
  change x*(p:G)*x⁻¹∈H ↔ (((p:G)*x⁻¹:G):G⧸H)=((x⁻¹:G):G⧸H)
  rw [QuotientGroup.eq]
  constructor
  · intro hp
    have hi := H.inv_mem hp
    convert hi using 1 <;> group
  · intro hp
    have hi := H.inv_mem hp
    convert hi using 1 <;> group

theorem inducedOrbitStabilizer_index (x : G) :
    (inducedOrbitStabilizer H P x).index=(MulAction.orbit P ((x⁻¹:G):G⧸H)).ncard := by
  rw [inducedOrbitStabilizer_eq,MulAction.index_stabilizer]

theorem inducedDoubleCosetOrbitEquiv_orbit
    (q : DoubleCoset.Quotient (H:Set G) (P:Set G)) :
    (inducedDoubleCosetOrbitEquiv H P q).orbit=
      MulAction.orbit P ((q.out⁻¹:G):G⧸H) := by
  have he : inducedDoubleCosetOrbitEquiv H P q=Quotient.mk'' ((q.out⁻¹:G):G⧸H) := by
    exact (congrArg (inducedDoubleCosetToOrbit H P) (DoubleCoset.out_eq' H P q)).symm
  rw [he,MulAction.orbitRel.Quotient.orbit_mk]

theorem inducedMackey_index_sum [Finite G]
    [Fintype (DoubleCoset.Quotient (H:Set G) (P:Set G))] :
    ∑q:DoubleCoset.Quotient (H:Set G) (P:Set G),
      (inducedOrbitStabilizer H P q.out).index=H.index := by
  letI : Fintype (MulAction.orbitRel.Quotient P (G⧸H)) := Fintype.ofFinite _
  calc
    _=∑q:DoubleCoset.Quotient (H:Set G) (P:Set G),
        Nat.card (inducedDoubleCosetOrbitEquiv H P q).orbit := by
      apply Finset.sum_congr rfl
      intro q _
      rw [inducedDoubleCosetOrbitEquiv_orbit,Nat.card_coe_set_eq,inducedOrbitStabilizer_index]
    _=∑o:MulAction.orbitRel.Quotient P (G⧸H),Nat.card o.orbit :=
      Fintype.sum_equiv (inducedDoubleCosetOrbitEquiv H P) _ _ (fun _ => rfl)
    _=Nat.card (G⧸H) := by
      rw [← Nat.card_sigma]
      exact Nat.card_congr (MulAction.selfEquivSigmaOrbits' P (G⧸H)).symm
    _=H.index := rfl

variable {P}

/-- The complete actual Mackey index list for an original Sylow
subgroup, with a common original-index valuation and exact total. -/
theorem inducedMackeySylow_indices [Finite G] (p : ℕ) [Fact p.Prime]
    (P : Sylow p G)
    [Fintype (DoubleCoset.Quotient (H:Set G) ((P:Subgroup G):Set G))] :
    ∃ j : DoubleCoset.Quotient (H:Set G) ((P:Subgroup G):Set G)→ℕ,
      (∀q,(inducedOrbitStabilizer H (P:Subgroup G) q.out).index=p^j q) ∧
      (∀q,H.index.factorization p≤j q) ∧
      ∑q,p^j q=H.index := by
  choose j hj hv using fun q : DoubleCoset.Quotient (H:Set G) ((P:Subgroup G):Set G) =>
    traceySylow_orbit_card p P ((q.out⁻¹:G):G⧸H)
  have hindex : ∀q,(inducedOrbitStabilizer H (P:Subgroup G) q.out).index=p^j q := by
    intro q
    rw [inducedOrbitStabilizer_index]
    exact hj q
  refine ⟨j,hindex,hv,?_⟩
  calc
    _=∑q:DoubleCoset.Quotient (H:Set G) ((P:Subgroup G):Set G),
        (inducedOrbitStabilizer H (P:Subgroup G) q.out).index :=
      Finset.sum_congr rfl (fun q _ => (hindex q).symm)
    _=H.index := inducedMackey_index_sum H (P:Subgroup G)

end SymmetricSubgroupAsymptotics
