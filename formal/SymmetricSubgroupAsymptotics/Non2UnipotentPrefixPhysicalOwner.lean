import SymmetricSubgroupAsymptotics.Non2UnipotentPrefixOwnerRecognition
import SymmetricSubgroupAsymptotics.Non2UnipotentPrefixPhysicalCover
import SymmetricSubgroupAsymptotics.FusionKernelAssembly

/-!
# The physical E7-UP-H/C owner

The historical unipotent-prefix insertion first consumes a complete physical
subgroup when any certified pointing is hot, then consumes the remaining
subgroups having a certified pointing.  The predicates below encode exactly
that union and priority on complete subgroups.  A displayed pointing retains
the original action, literal normal axis, complete complement, quotient map,
and physical relabelling; auxiliary witnesses are existential and hence add
no counted multiplicity.

The universal `47/48` certificate constructed from the chosen physical pair
frame supplies such a pointing.  Therefore the concrete two-branch owner
satisfies the narrowed recognition interface, and every appended residual
axis fibre is empty without an assumed semantic owner bridge.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu

/-- The complete subgroup reconstructed from one literal menu action, normal
axis, complete exterior source, and quotient epimorphism. -/
def e7UPReconstruction
    (i : ActionIndex) {b : ℕ}
    (N : {N : Subgroup (sourceAction i) // N.Normal})
    (J : Subgroup (Equiv.Perm (Fin b)))
    (β : GroupEpimorphism J (sourceAction i ⧸ N.1)) :
    Subgroup (Equiv.Perm (Fin (2 * pairCount i + b))) :=
  relabelSubgroup finSumFinEquiv
    ((fusionFullGoursatEncode N J β).1.map
      (fusionOrbitAction (sourceAction i)))

/-- A complete subgroup has a displayed E7-UP certified pointing.  The
payload is the canonical one constructed from the chosen physical pair frame.
-/
def E7UPCertifiedPhysical
    (hTracey : TraceyBinaryFormulaInput)
    (hExceptional : TraceyBinaryExceptionalThreeInput)
    (n : ℕ) (H : Subgroup (Equiv.Perm (Fin n))) : Prop :=
  ∃ (i : ActionIndex) (b : ℕ)
    (e : Fin (2 * pairCount i + b) ≃ Fin n)
    (N : {N : Subgroup (sourceAction i) // N.Normal})
    (J : Subgroup (Equiv.Perm (Fin b)))
    (β : GroupEpimorphism J (sourceAction i ⧸ N.1)),
      H = relabelSubgroup e (e7UPReconstruction i N J β) ∧
        FixedCutUPCertified
          (axisPayload hTracey hExceptional i N).M (pairCount i)

/-- The historical hot branch: some certified pointing has weight above its
literal threshold.  This is an existential over all displayed pointings, so
the subsequent cold branch implements the original ANY-hot priority. -/
def E7UPHotPhysical
    (hTracey : TraceyBinaryFormulaInput)
    (hExceptional : TraceyBinaryExceptionalThreeInput)
    (n : ℕ) (H : Subgroup (Equiv.Perm (Fin n))) : Prop :=
  ∃ (i : ActionIndex) (b : ℕ)
    (e : Fin (2 * pairCount i + b) ≃ Fin n)
    (N : {N : Subgroup (sourceAction i) // N.Normal})
    (J : Subgroup (Equiv.Perm (Fin b)))
    (β : GroupEpimorphism J (sourceAction i ⧸ N.1)),
      H = relabelSubgroup e (e7UPReconstruction i N J β) ∧
        FixedCutUPCertified
          (axisPayload hTracey hExceptional i N).M (pairCount i) ∧
        fusionLocalThreshold b
            (axisPayload hTracey hExceptional i N).certificate.prefixDegree
            (axisPayload hTracey hExceptional i N).certificate.gapParameter <
          (axisPayload hTracey hExceptional i N).certificate.momentWeight J

/-- The historical cold branch is the certified remainder after the global
ANY-hot branch. -/
def E7UPColdPhysical
    (hTracey : TraceyBinaryFormulaInput)
    (hExceptional : TraceyBinaryExceptionalThreeInput)
    (n : ℕ) (H : Subgroup (Equiv.Perm (Fin n))) : Prop :=
  E7UPCertifiedPhysical hTracey hExceptional n H ∧
    ¬ E7UPHotPhysical hTracey hExceptional n H

theorem e7UPCertifiedPhysical_hot_or_cold
    (hTracey : TraceyBinaryFormulaInput)
    (hExceptional : TraceyBinaryExceptionalThreeInput)
    {n : ℕ} {H : Subgroup (Equiv.Perm (Fin n))}
    (hH : E7UPCertifiedPhysical hTracey hExceptional n H) :
    E7UPHotPhysical hTracey hExceptional n H ∨
      E7UPColdPhysical hTracey hExceptional n H := by
  by_cases hhot : E7UPHotPhysical hTracey hExceptional n H
  · exact Or.inl hhot
  · exact Or.inr ⟨hH, hhot⟩

theorem e7UPCertifiedPhysical_relabel_iff
    (hTracey : TraceyBinaryFormulaInput)
    (hExceptional : TraceyBinaryExceptionalThreeInput)
    {m n : ℕ} (hmn : m = n) (e : Fin m ≃ Fin n)
    (H : Subgroup (Equiv.Perm (Fin m))) :
    E7UPCertifiedPhysical hTracey hExceptional n (relabelSubgroup e H) ↔
      E7UPCertifiedPhysical hTracey hExceptional m H := by
  subst n
  constructor
  · rintro ⟨i, b, c, N, J, β, hc, hcut⟩
    refine ⟨i, b, c.trans e.symm, N, J, β, ?_, hcut⟩
    calc
      H = relabelSubgroup e.symm (relabelSubgroup e H) :=
        (relabelSubgroup_symm e H).symm
      _ = relabelSubgroup e.symm
          (relabelSubgroup c (e7UPReconstruction i N J β)) := by rw [hc]
      _ = relabelSubgroup (c.trans e.symm)
          (e7UPReconstruction i N J β) := by rw [relabelSubgroup_trans]
  · rintro ⟨i, b, c, N, J, β, hc, hcut⟩
    refine ⟨i, b, c.trans e, N, J, β, ?_, hcut⟩
    calc
      relabelSubgroup e H = relabelSubgroup e
          (relabelSubgroup c (e7UPReconstruction i N J β)) := by rw [hc]
      _ = relabelSubgroup (c.trans e)
          (e7UPReconstruction i N J β) := by rw [relabelSubgroup_trans]

theorem e7UPHotPhysical_relabel_iff
    (hTracey : TraceyBinaryFormulaInput)
    (hExceptional : TraceyBinaryExceptionalThreeInput)
    {m n : ℕ} (hmn : m = n) (e : Fin m ≃ Fin n)
    (H : Subgroup (Equiv.Perm (Fin m))) :
    E7UPHotPhysical hTracey hExceptional n (relabelSubgroup e H) ↔
      E7UPHotPhysical hTracey hExceptional m H := by
  subst n
  constructor
  · rintro ⟨i, b, c, N, J, β, hc, hcut, hhot⟩
    refine ⟨i, b, c.trans e.symm, N, J, β, ?_, hcut, hhot⟩
    calc
      H = relabelSubgroup e.symm (relabelSubgroup e H) :=
        (relabelSubgroup_symm e H).symm
      _ = relabelSubgroup e.symm
          (relabelSubgroup c (e7UPReconstruction i N J β)) := by rw [hc]
      _ = relabelSubgroup (c.trans e.symm)
          (e7UPReconstruction i N J β) := by rw [relabelSubgroup_trans]
  · rintro ⟨i, b, c, N, J, β, hc, hcut, hhot⟩
    refine ⟨i, b, c.trans e, N, J, β, ?_, hcut, hhot⟩
    calc
      relabelSubgroup e H = relabelSubgroup e
          (relabelSubgroup c (e7UPReconstruction i N J β)) := by rw [hc]
      _ = relabelSubgroup (c.trans e)
          (e7UPReconstruction i N J β) := by rw [relabelSubgroup_trans]

theorem e7UPColdPhysical_relabel_iff
    (hTracey : TraceyBinaryFormulaInput)
    (hExceptional : TraceyBinaryExceptionalThreeInput)
    {m n : ℕ} (hmn : m = n) (e : Fin m ≃ Fin n)
    (H : Subgroup (Equiv.Perm (Fin m))) :
    E7UPColdPhysical hTracey hExceptional n (relabelSubgroup e H) ↔
      E7UPColdPhysical hTracey hExceptional m H := by
  unfold E7UPColdPhysical
  rw [e7UPCertifiedPhysical_relabel_iff hTracey hExceptional hmn e H,
    e7UPHotPhysical_relabel_iff hTracey hExceptional hmn e H]

inductive E7UPOwnerKind
  | hot | cold
  deriving DecidableEq, Fintype

def E7UPOwnerKind.property
    (hTracey : TraceyBinaryFormulaInput)
    (hExceptional : TraceyBinaryExceptionalThreeInput)
    (k : E7UPOwnerKind) (n : ℕ)
    (H : Subgroup (Equiv.Perm (Fin n))) : Prop :=
  match k with
  | .hot => E7UPHotPhysical hTracey hExceptional n H
  | .cold => E7UPColdPhysical hTracey hExceptional n H

def e7UPOwnerKindEquiv : Fin 2 ≃ E7UPOwnerKind :=
  (Fintype.equivFin E7UPOwnerKind).symm

/-- The two historical E7-UP-H/C branches as a concrete earlier-owner menu. -/
def e7UPPhysicalOwnerMenu
    (hTracey : TraceyBinaryFormulaInput)
    (hExceptional : TraceyBinaryExceptionalThreeInput)
    (n : ℕ) (j : Fin 2)
    (H : Subgroup (Equiv.Perm (Fin n))) : Prop :=
  (e7UPOwnerKindEquiv j).property hTracey hExceptional n H

theorem e7UPPhysicalOwnerMenu_natural
    (hTracey : TraceyBinaryFormulaInput)
    (hExceptional : TraceyBinaryExceptionalThreeInput) :
    DegreeNaturalOwnerMenu
      (e7UPPhysicalOwnerMenu hTracey hExceptional) := by
  intro m n hmn e j H
  cases hk : e7UPOwnerKindEquiv j with
  | hot =>
      simpa only [e7UPPhysicalOwnerMenu, hk, E7UPOwnerKind.property] using
        (e7UPHotPhysical_relabel_iff
          hTracey hExceptional hmn e H)
  | cold =>
      simpa only [e7UPPhysicalOwnerMenu, hk, E7UPOwnerKind.property] using
        (e7UPColdPhysical_relabel_iff
          hTracey hExceptional hmn e H)

/-- The canonical framed `47/48` cut places every literal reconstruction in
the concrete hot/cold owner union. -/
theorem e7UPPhysicalOwnerMenu_recognizes
    (hTracey : TraceyBinaryFormulaInput)
    (hExceptional : TraceyBinaryExceptionalThreeInput) :
    OwnerRecognizes (e7UPPhysicalOwnerMenu hTracey hExceptional)
      hTracey hExceptional := by
  intro i N hcut b J β
  let H := e7UPReconstruction i N J β
  have hcert : E7UPCertifiedPhysical hTracey hExceptional
      (2 * pairCount i + b) H := by
    refine ⟨i, b, Equiv.refl _, N, J, β, ?_, hcut⟩
    exact (relabelSubgroup_refl H).symm
  rcases e7UPCertifiedPhysical_hot_or_cold
      hTracey hExceptional hcert with hhot | hcold
  · refine ⟨e7UPOwnerKindEquiv.symm .hot, ?_⟩
    simpa only [e7UPPhysicalOwnerMenu, Equiv.apply_symm_apply,
      E7UPOwnerKind.property, EarlierLocal, H, e7UPReconstruction] using hhot
  · refine ⟨e7UPOwnerKindEquiv.symm .cold, ?_⟩
    simpa only [e7UPPhysicalOwnerMenu, Equiv.apply_symm_apply,
      E7UPOwnerKind.property, EarlierLocal, H, e7UPReconstruction] using hcold

/-- No full local subgroup can be first-owned by the appended residual branch
after the concrete E7-UP-H/C menu: its literal Goursat axis and source map
reconstruct a certified pointing already owned by one of the two branches. -/
theorem not_e7UPResidualAccepted
    (hTracey : TraceyBinaryFormulaInput)
    (hExceptional : TraceyBinaryExceptionalThreeInput)
    (i : ActionIndex) (b : ℕ)
    (L : Subgroup (sourceAction i × Equiv.Perm (Fin b))) :
    ¬ FusionAcceptedOrbitPredicate (sourceAction i)
        (ordinaryFirstOwnerLocalPredicate (sourceAction i)
          (ownerOrResidualEligible
            (e7UPPhysicalOwnerMenu hTracey hExceptional)
            (2 * pairCount i + b))
          (Fin.last 2)) L := by
  rintro ⟨hfull, hresidual⟩
  let F : FusionFullSubgroups (sourceAction i) (Equiv.Perm (Fin b)) :=
    ⟨L, hfull⟩
  let d := (fusionFullGoursatEquiv
    (U := sourceAction i) (G := Equiv.Perm (Fin b))) F
  rcases hd : d with ⟨N, J, β⟩
  have hdecode := (fusionFullGoursatEquiv
    (U := sourceAction i) (G := Equiv.Perm (Fin b))).symm_apply_apply F
  change (fusionFullGoursatEquiv
    (U := sourceAction i) (G := Equiv.Perm (Fin b))).symm d = F at hdecode
  rw [hd, fusionFullGoursatEquiv_symm] at hdecode
  have hL : (fusionFullGoursatEncode N J β).1 = L :=
    congrArg (fun X : FusionFullSubgroups
      (sourceAction i) (Equiv.Perm (Fin b)) => X.1) hdecode
  have hnone : ∀ j : Fin 2,
      ¬ e7UPPhysicalOwnerMenu hTracey hExceptional
        (2 * pairCount i + b) j
        (relabelSubgroup finSumFinEquiv
          (L.map (fusionOrbitAction (sourceAction i)))) :=
    (firstOwned_ownerOrResidual_last_iff
      (e7UPPhysicalOwnerMenu hTracey hExceptional) _).mp hresidual.2
  obtain ⟨j, hj⟩ := e7UPPhysicalOwnerMenu_recognizes
    hTracey hExceptional i N
      (axisPayload_fixedCutUPCertified hTracey hExceptional i N) b J β
  apply hnone j
  rw [← hL]
  exact hj

/-- The entire labelled residual family on one fixed menu action is empty.
This is a set-theoretic zero statement before any numerical row is charged. -/
theorem e7UPResidualOrbitFamily_eq_empty
    (hTracey : TraceyBinaryFormulaInput)
    (hExceptional : TraceyBinaryExceptionalThreeInput)
    (i : ActionIndex) (b : ℕ) :
    FusionOrbitFamily (sourceAction i)
      (FusionAcceptedOrbitPredicate (sourceAction i)
        (ordinaryFirstOwnerLocalPredicate (sourceAction i)
          (ownerOrResidualEligible
            (e7UPPhysicalOwnerMenu hTracey hExceptional)
            (2 * pairCount i + b))
          (Fin.last 2))) = ∅ := by
  ext K
  constructor
  · intro hK
    obtain ⟨⟨e, ⟨M, hM⟩⟩, rfl⟩ := hK
    obtain ⟨L, rfl⟩ := hM
    exact False.elim
      (not_e7UPResidualAccepted hTracey hExceptional i b L.1 L.2)
  · intro hK
    exact False.elim hK

/-- The corresponding canonical physical family is empty in every ambient
degree.  Its original action and complete complement are unchanged. -/
theorem e7UPResidualWidthCanonicalFamily_eq_empty
    (hTracey : TraceyBinaryFormulaInput)
    (hExceptional : TraceyBinaryExceptionalThreeInput)
    (i : ActionIndex) {n : ℕ} (hn : i.1.sourceDegree ≤ n) :
    FusionWidthCanonicalFamily i.2.1.representative hn
      (non2FirstOwnerPredicate
        (ownerOrResidualEligible
          (e7UPPhysicalOwnerMenu hTracey hExceptional))
        i.1.sourceDegree (Fin.last 2, i.2.1)
          (n - i.1.sourceDegree)) = ∅ := by
  unfold FusionWidthCanonicalFamily
  have hempty := e7UPResidualOrbitFamily_eq_empty
    hTracey hExceptional i (n - i.1.sourceDegree)
  simp only [sourceAction, pairCount, PairCountLabel.sourceDegree,
    non2FirstOwnerPredicate, non2FirstOwnerAction] at hempty ⊢
  rw [hempty]
  simp [FusionRelabelledFamily]
  rfl

/-- Complete selected-entry exhaustion: a noncritical physical subgroup that
contains a historical eight-width selected UP pair orbit cannot be first-owned
by the appended residual branch after E7-UP-H/C. -/
theorem not_firstOwned_e7UPResidual_of_selectedUPPairOrbit
    (hTracey : TraceyBinaryFormulaInput)
    (hExceptional : TraceyBinaryExceptionalThreeInput)
    {n : ℕ} (H : Subgroup (Equiv.Perm (Fin n)))
    (hordinary : ¬ IsCriticalSubgroup n H)
    (hUP : HasSelectedUPPairOrbit H) :
    ¬ FirstOwned
        (ownerOrResidualEligible
          (e7UPPhysicalOwnerMenu hTracey hExceptional) n)
        (Fin.last 2) H := by
  intro howner
  obtain ⟨i, hn, hmem⟩ :=
    selectedUPPairOrbit_mem_residualCanonicalFamily
      (e7UPPhysicalOwnerMenu hTracey hExceptional)
      (e7UPPhysicalOwnerMenu_natural hTracey hExceptional)
      H hordinary howner hUP
  rw [e7UPResidualWidthCanonicalFamily_eq_empty
    hTracey hExceptional i hn] at hmem
  exact hmem

/-- Exact zero payment for every axis after the concrete E7-UP-H/C owner is
placed before the appended residual branch. -/
theorem residualEpiCount_eq_zero_after_e7UPPhysicalOwner
    (hTracey : TraceyBinaryFormulaInput)
    (hExceptional : TraceyBinaryExceptionalThreeInput)
    {b : ℕ} (i : ActionIndex)
    (N : {N : Subgroup (sourceAction i) // N.Normal})
    (J : Subgroup (Equiv.Perm (Fin b))) :
    fusionSurvivingEpiCount (sourceAction i)
        (ordinaryFirstOwnerLocalPredicate (sourceAction i)
          (ownerOrResidualEligible
            (e7UPPhysicalOwnerMenu hTracey hExceptional)
            (2 * pairCount i + b))
          (Fin.last 2)) N J = 0 :=
  residualEpiCount_eq_zero_of_ownerRecognition
    (e7UPPhysicalOwnerMenu hTracey hExceptional)
    hTracey hExceptional
    (e7UPPhysicalOwnerMenu_recognizes hTracey hExceptional) i N J

end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
