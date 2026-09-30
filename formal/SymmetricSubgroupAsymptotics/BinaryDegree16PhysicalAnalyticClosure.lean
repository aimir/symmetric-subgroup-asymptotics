import SymmetricSubgroupAsymptotics.BinaryDegree16CarrierRouting
import SymmetricSubgroupAsymptotics.BinaryTransitivePowerSevenBoundary
import SymmetricSubgroupAsymptotics.FusionActualOrbitCharts

/-!
# Physical degree-sixteen axes reach the analytic closure

An actual sixteen-point binary orbit of an arbitrary permutation subgroup is
put in the canonical orbit/complement chart.  Its complete two-coordinate
model retains the entire complementary action and all correlations with it.
The literal Goursat axis of that model is then sent through the completed
degree-sixteen split theorem.

This is the physical bridge from an unmarked original subgroup to the finite
analytic dichotomy.  It does not choose a catalogue representative as part of
the counted object and it does not discard the exterior coordinate.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical Pointwise

namespace SymmetricSubgroupAsymptotics.BinaryDegree16PhysicalAnalyticClosure

open SymmetricSubgroupAsymptotics
open BinaryDegree16SplitAnalyticClosure
open BinaryDegree16CarrierRouting
open BinaryDegreeEightPhysicalAnalyticClosure

section CoordinateEquivalence

variable {A B G : Type*} [Group A] [Group B] [Group G]

/-- Full first projection is preserved when the first coordinate is changed
to an isomorphic group type. -/
theorem fusion_full_map_prod_equiv (K : Subgroup (A × G))
    (hK : K.map (MonoidHom.fst A G) = ⊤) (e : A ≃* B) (f : G ≃* G) :
    (K.map (e.prodCongr f).toMonoidHom).map (MonoidHom.fst B G) = ⊤ := by
  rw [Subgroup.map_map]
  have he : (MonoidHom.fst B G).comp (e.prodCongr f).toMonoidHom =
      e.toMonoidHom.comp (MonoidHom.fst A G) := by
    ext x
    rfl
  rw [he, ← Subgroup.map_map, hK]
  exact Subgroup.map_top_of_surjective _ e.surjective

/-- The Goursat axis changes by the same first-coordinate equivalence. -/
theorem fusion_axis_map_prod_equiv (K : Subgroup (A × G))
    (e : A ≃* B) (f : G ≃* G) :
    (K.map (e.prodCongr f).toMonoidHom).goursatFst =
      K.goursatFst.map e.toMonoidHom := by
  ext b
  rw [Subgroup.mem_goursatFst]
  constructor
  · rintro ⟨⟨x,y⟩,hxy,heq⟩
    have hx : e x = b := congrArg Prod.fst heq
    have hy : f y = 1 := congrArg (fun z : B × G => z.2) heq
    have hy' : y = 1 := f.injective (hy.trans f.map_one.symm)
    subst y
    exact ⟨x,Subgroup.mem_goursatFst.mpr hxy,hx⟩
  · rintro ⟨x,hx,heq⟩
    exact ⟨(x,1),Subgroup.mem_goursatFst.mp hx,
      by simpa using Prod.ext heq f.map_one⟩

/-- A first-coordinate equivalence and an automorphism of the exterior carry
the complete exterior image exactly. -/
theorem fusion_complement_map_prod_equiv (K : Subgroup (A × G))
    (e : A ≃* B) (f : G ≃* G) :
    (K.map (e.prodCongr f).toMonoidHom).map (MonoidHom.snd B G) =
      (K.map (MonoidHom.snd A G)).map f.toMonoidHom := by
  rw [Subgroup.map_map,Subgroup.map_map]
  congr 1

end CoordinateEquivalence

/-- An intrinsic sixteen-point orbit of the original subgroup, together with
binaryity of its actual faithful restriction image. -/
structure OrbitWitness {n : ℕ} (H : Subgroup (Equiv.Perm (Fin n))) where
  point : Fin n
  orbit_card : Nat.card (MulAction.orbit H point) = 16
  binary : IsPGroup 2 (FusionActualOrbitCharts.orbitImage H point)

namespace OrbitWitness

variable {n : ℕ} {H : Subgroup (Equiv.Perm (Fin n))} (W : OrbitWitness H)

/-- The canonical chart made from the actual orbit and its full complement. -/
def chart : Fin 16 ⊕ Fin (n-16) ≃ Fin n :=
  FusionActualOrbitCharts.chart H W.point W.orbit_card

/-- The literal first projection in that chart. -/
def action : Subgroup (Equiv.Perm (Fin 16)) :=
  FusionActualOrbitCharts.chartAction H W.point W.orbit_card

/-- The complete original subgroup in orbit/complement coordinates. -/
def pulled : Subgroup (Equiv.Perm (Fin 16 ⊕ Fin (n-16))) :=
  relabelSubgroup W.chart.symm H

/-- The complete Goursat model.  Its second coordinate is the whole exterior
permutation action, with arbitrary correlations retained. -/
def model : Subgroup (W.action × Equiv.Perm (Fin (n-16))) :=
  fusionDeletedModel W.action W.pulled

theorem degree_le (W : OrbitWitness H) : 16 ≤ n :=
  FusionActualOrbitCharts.degree_le H W.point W.orbit_card

theorem action_binary : IsPGroup 2 W.action :=
  FusionActualOrbitCharts.chartAction_isPGroup H W.point W.orbit_card 2 W.binary

instance action_pretransitive : MulAction.IsPretransitive W.action (Fin 16) :=
  FusionActualOrbitCharts.chartAction_transitive H W.point W.orbit_card

theorem pulled_preserves :
    ∀ k ∈ W.pulled,
      Set.MapsTo k (Set.range (Sum.inl : Fin 16 → Fin 16 ⊕ Fin (n-16)))
        (Set.range (Sum.inl : Fin 16 → Fin 16 ⊕ Fin (n-16))) :=
  FusionActualOrbitCharts.chart_preserves H W.point W.orbit_card

theorem first_projection :
    (fusionPhysicalBlockPullback W.pulled).map
      (MonoidHom.fst (Equiv.Perm (Fin 16)) (Equiv.Perm (Fin (n-16)))) = W.action :=
  rfl

theorem model_full :
    W.model.map (MonoidHom.fst W.action (Equiv.Perm (Fin (n-16)))) = ⊤ :=
  fusionDeletedModel_full W.action W.pulled W.first_projection

theorem model_recovers :
    W.model.map (fusionOrbitAction W.action) = W.pulled :=
  fusionDeletedModel_recovers W.action W.pulled W.pulled_preserves W.first_projection

/-- The literal normal axis attached to the actual complete exterior model. -/
def axis : Subgroup W.action := W.model.goursatFst

instance axis_normal : W.axis.Normal :=
  Subgroup.normal_goursatFst (by
    intro u
    have hu : u ∈ W.model.map
        (MonoidHom.fst W.action (Equiv.Perm (Fin (n-16)))) := by
      rw [W.model_full]
      trivial
    obtain ⟨x,hx,he⟩ := hu
    exact ⟨⟨x,hx⟩,he⟩)

/-- The actual local axis reaches either a direct original-weight entry or
one of the exact carrier-mixture consumers. -/
theorem analytic_owner : AnalyticOwner W.action W.axis :=
  complete_axis_analytic W.action W.action_binary W.axis

/-- The exact physical axis already reaches one of the two final consumers. -/
theorem direct_or_carrier :
    DirectOwner W.action W.axis ∨ CarrierOwner W.action W.axis :=
  W.analytic_owner.direct_or_carrier

/-- The physical degree-sixteen axis reaches direct continuation or an exact
positive-support slot on its unchanged local action. -/
theorem direct_or_supported_slot :
    DirectOwner W.action W.axis ∨
      Nonempty {S : AxisSlot W.action W.axis // S.HasNoncritical} :=
  complete_axis_direct_or_supported_slot W.action W.action_binary W.axis

/-- Change only the labels on the selected orbit.  The exterior coordinate
is carried by the identity, so this is the local model used when an analytic
owner supplies a conjugate catalogue action. -/
def conjugatedModel (g : Equiv.Perm (Fin 16))
    {V : Subgroup (Equiv.Perm (Fin 16))}
    (hg : MulAut.conj g • W.action = V) :
    Subgroup (V × Equiv.Perm (Fin (n-16))) :=
  W.model.map (((actionConjugacyEquiv g hg).prodCongr
    (MulEquiv.refl (Equiv.Perm (Fin (n-16))))).toMonoidHom)

theorem conjugatedModel_full (g : Equiv.Perm (Fin 16))
    {V : Subgroup (Equiv.Perm (Fin 16))}
    (hg : MulAut.conj g • W.action = V) :
    (W.conjugatedModel g hg).map
      (MonoidHom.fst V (Equiv.Perm (Fin (n-16)))) = ⊤ := by
  exact fusion_full_map_prod_equiv W.model W.model_full (actionConjugacyEquiv g hg)
    (MulEquiv.refl (Equiv.Perm (Fin (n-16))))

/-- The normal axis is transported by the same ambient point conjugacy as
the original action. -/
theorem conjugatedModel_axis (g : Equiv.Perm (Fin 16))
    {V : Subgroup (Equiv.Perm (Fin 16))}
    (hg : MulAut.conj g • W.action = V) :
    (W.conjugatedModel g hg).goursatFst =
      actionConjugacyNormal g hg W.axis := by
  exact fusion_axis_map_prod_equiv W.model (actionConjugacyEquiv g hg)
    (MulEquiv.refl (Equiv.Perm (Fin (n-16))))

/-- The complete exterior subgroup, including every correlation visible in
its image, is literally unchanged by the orbit relabelling. -/
theorem conjugatedModel_exterior (g : Equiv.Perm (Fin 16))
    {V : Subgroup (Equiv.Perm (Fin 16))}
    (hg : MulAut.conj g • W.action = V) :
    (W.conjugatedModel g hg).map
        (MonoidHom.snd V (Equiv.Perm (Fin (n-16)))) =
      W.model.map (MonoidHom.snd W.action (Equiv.Perm (Fin (n-16)))) := by
  simpa using fusion_complement_map_prod_equiv W.model (actionConjugacyEquiv g hg)
    (MulEquiv.refl (Equiv.Perm (Fin (n-16))))

/-- Reconstruction on the original labels: the analytic owner is attached
to a model whose image is exactly the original subgroup after undoing the
canonical chart. -/
theorem recovers_original :
    relabelSubgroup W.chart (W.model.map (fusionOrbitAction W.action)) = H := by
  rw [W.model_recovers]
  simp only [pulled, relabelSubgroup_trans, Equiv.symm_trans_self,
    relabelSubgroup_refl]

end OrbitWitness

/-- The unmarked physical sector: membership records only the existence of
an actual binary orbit of size sixteen. -/
def physicalFamily (n : ℕ) : Set (Subgroup (Equiv.Perm (Fin n))) :=
  {H | Nonempty (OrbitWitness H)}

/-- The unmarked subfamily for which at least one actual sixteen-point orbit
has a direct axis.  The orbit and its chart are existential witnesses, not
extra multiplicities in the counted object. -/
def directFamily (n : ℕ) : Set (Subgroup (Equiv.Perm (Fin n))) :=
  {H | ∃ W : OrbitWitness H, DirectOwner W.action W.axis}

/-- The exact complement of the direct family inside the physical sector. -/
def carrierResidualFamily (n : ℕ) : Set (Subgroup (Equiv.Perm (Fin n))) :=
  {H | H ∈ physicalFamily n ∧ H ∉ directFamily n}

theorem directFamily_subset (n : ℕ) : directFamily n ⊆ physicalFamily n := by
  rintro H ⟨W,_⟩
  exact ⟨W⟩

/-- On the residual side every possible eligible physical witness is a
carrier witness.  This is stronger than choosing one carrier orbit and is the
quantifier needed before all replacements are made simultaneously. -/
theorem carrierResidual_all_witnesses {n : ℕ}
    {H : Subgroup (Equiv.Perm (Fin n))}
    (hH : H ∈ carrierResidualFamily n) (W : OrbitWitness H) :
    CarrierOwner W.action W.axis := by
  rcases W.direct_or_carrier with hdirect | hcarrier
  · exact False.elim (hH.2 ⟨W,hdirect⟩)
  · exact hcarrier

/-- Every eligible orbit of a residual physical subgroup supplies an exact
positive-support slot, ready for simultaneous routed-word assembly. -/
theorem carrierResidual_all_supported_slots {n : ℕ}
    {H : Subgroup (Equiv.Perm (Fin n))}
    (hH : H ∈ carrierResidualFamily n) (W : OrbitWitness H) :
    Nonempty {S : AxisSlot W.action W.axis // S.HasNoncritical} := by
  rcases W.direct_or_supported_slot with hdirect | hslot
  · exact False.elim (hH.2 ⟨W,hdirect⟩)
  · exact hslot

/-- A residual carrier orbit is automatically beyond the already completed
small-order boundary.  Thus the physical split introduces no duplicate
ownership with the order-at-most-256 degree-sixteen recurrence. -/
theorem carrierResidual_action_order_gt {n : ℕ}
    {H : Subgroup (Equiv.Perm (Fin n))}
    (hH : H ∈ carrierResidualFamily n) (W : OrbitWitness H) :
    256 < Nat.card W.action := by
  by_contra hlarge
  have hcard : Nat.card W.action ≤ 256 := Nat.le_of_not_gt hlarge
  let C : BinaryOrderSevenCharacterSelection W.action :=
    BinaryTransitivePowerSevenBoundary.selectionOfDegree
      4 (by decide) W.action (by norm_num) (by simpa using hcard)
  have haccepted : BinaryDegree16SplitFrontier.AcceptedAxis W.action W.axis :=
    Or.inr ⟨C ⟨W.axis,inferInstance⟩⟩
  exact hH.2 ⟨W,DirectOwner.accepted haccepted⟩

/-- Every physical subgroup is either directly owned or lies in the exact
all-carrier residual family. -/
theorem direct_or_carrierResidual {n : ℕ}
    {H : Subgroup (Equiv.Perm (Fin n))} (hH : H ∈ physicalFamily n) :
    H ∈ directFamily n ∨ H ∈ carrierResidualFamily n := by
  by_cases hdirect : H ∈ directFamily n
  · exact Or.inl hdirect
  · exact Or.inr ⟨hH,hdirect⟩

/-- Family-level upper partition on the original subgroups.  No orbit, point,
chart, action, or axis witness is charged as a counted marking. -/
theorem physical_card_le_direct_add_carrierResidual (n : ℕ) :
    Nat.card (physicalFamily n) ≤
      Nat.card (directFamily n) + Nat.card (carrierResidualFamily n) := by
  let A : Bool → Set (Subgroup (Equiv.Perm (Fin n))) := fun b =>
    if b then carrierResidualFamily n else directFamily n
  have h := fusionPhysicalUnion_card_le (physicalFamily n) A (by
    intro H hH
    rcases direct_or_carrierResidual hH with hd | hc
    · exact ⟨false,hd⟩
    · exact ⟨true,hc⟩)
  simpa [A,add_comm] using h

/-- A counting-ready physical record.  The original subgroup itself remains
the object being counted; the witness merely exposes its exact local axis and
analytic destination. -/
structure PhysicalRecord {n : ℕ} (H : Subgroup (Equiv.Perm (Fin n))) where
  witness : OrbitWitness H
  owner : AnalyticOwner witness.action witness.axis

theorem physical_record_nonempty {n : ℕ}
    (H : Subgroup (Equiv.Perm (Fin n))) (hH : H ∈ physicalFamily n) :
    Nonempty (PhysicalRecord H) := by
  obtain ⟨W⟩ := hH
  exact ⟨⟨W,W.analytic_owner⟩⟩

/-- The same record explicitly retains literal reconstruction of the original
subgroup through the chosen complete exterior model. -/
theorem physical_record_recovers {n : ℕ}
    {H : Subgroup (Equiv.Perm (Fin n))} (R : PhysicalRecord H) :
    relabelSubgroup R.witness.chart
      (R.witness.model.map (fusionOrbitAction R.witness.action)) = H :=
  R.witness.recovers_original

end SymmetricSubgroupAsymptotics.BinaryDegree16PhysicalAnalyticClosure

end
