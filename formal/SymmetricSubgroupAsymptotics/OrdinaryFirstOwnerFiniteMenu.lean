import SymmetricSubgroupAsymptotics.OrdinaryRemainderNaturality
import SymmetricSubgroupAsymptotics.BinaryFiniteEntryFusion
import SymmetricSubgroupAsymptotics.FusionPhysicalUnion
import SymmetricSubgroupAsymptotics.FusionPhysicalFilters

/-! First ownership is a predicate of the complete physical subgroup. Its
pullback supplies original-normalizer naturality to the checked binary
finite-menu bound. Literal ownership-to-local-family coverage and all
remaining branch envelopes and moments are explicit inputs. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics

/-- Earlier exclusions are evaluated on the entire physical subgroup,
including the original action and the untouched complete complement. -/
def ordinaryFirstOwnerLocalPredicate {w b r : ℕ}
    (U : Subgroup (Equiv.Perm (Fin w)))
    (Eligible : Fin r → Subgroup (Equiv.Perm (Fin (w+b))) → Prop)
    (i : Fin r) (H : Subgroup (U × Equiv.Perm (Fin b))) : Prop :=
  ordinaryRemainderFusionPredicate U H ∧ FirstOwned Eligible i
    (relabelSubgroup (finSumFinEquiv : Fin w ⊕ Fin b ≃ Fin (w+b))
      (H.map (fusionOrbitAction (Z := Fin b) U)))

theorem ordinaryFirstOwnerLocalPredicate_natural {w b r : ℕ}
    (U : Subgroup (Equiv.Perm (Fin w)))
    (Eligible : Fin r → Subgroup (Equiv.Perm (Fin (w+b))) → Prop)
    (hEligible : ∀ i (s : Equiv.Perm (Fin (w+b))) H,
      Eligible i (relabelSubgroup s H) ↔ Eligible i H) (i : Fin r) :
    FusionOrbitNatural U (ordinaryFirstOwnerLocalPredicate U Eligible i) :=
  ordinaryRemainder_firstOwnerFusion_natural U Eligible hEligible i

/-- The actual local fusion family, placed on the same physical labelled
set as the first-owner predicate. No quotient by conjugacy is taken. -/
def ordinaryFirstOwnerPhysicalFamily {w b r : ℕ}
    (U : Subgroup (Equiv.Perm (Fin w)))
    (Eligible : Fin r → Subgroup (Equiv.Perm (Fin (w+b))) → Prop) (i : Fin r) :
    Set (Subgroup (Equiv.Perm (Fin (w+b)))) :=
  FusionRelabelledFamily (finSumFinEquiv : Fin w ⊕ Fin b ≃ Fin (w+b))
    (FusionOrbitFamily U
      (FusionAcceptedOrbitPredicate U (ordinaryFirstOwnerLocalPredicate U Eligible i)))

theorem ordinaryFirstOwnerPhysicalFamily_card {w b r : ℕ}
    (U : Subgroup (Equiv.Perm (Fin w)))
    (Eligible : Fin r → Subgroup (Equiv.Perm (Fin (w+b))) → Prop) (i : Fin r) :
    Nat.card (ordinaryFirstOwnerPhysicalFamily U Eligible i) =
      Nat.card (FusionOrbitFamily U
        (FusionAcceptedOrbitPredicate U (ordinaryFirstOwnerLocalPredicate U Eligible i))) :=
  fusionRelabelledFamily_card _ _

/-- The full original action with arbitrary complete complement, before
imposing noncriticality or first ownership. Every local subgroup has full
projection onto the original U. -/
def ordinaryFullOrbitPhysicalFamily {w b : ℕ}
    (U : Subgroup (Equiv.Perm (Fin w))) :
    Set (Subgroup (Equiv.Perm (Fin (w+b)))) :=
  FusionRelabelledFamily (finSumFinEquiv : Fin w ⊕ Fin b ≃ Fin (w+b))
    (FusionOrbitFamily U (fun H => H.map (MonoidHom.fst U (Equiv.Perm (Fin b)))=⊤))

/-- Physicalization commutes with the complete noncritical first-owner
filter. Earlier exclusions are imposed on the full physical subgroup. -/
theorem ordinaryFirstOwnerPhysicalFamily_eq_filter {w b r : ℕ}
    (U : Subgroup (Equiv.Perm (Fin w)))
    (Eligible : Fin r → Subgroup (Equiv.Perm (Fin (w+b))) → Prop)
    (hEligible : ∀ i (s : Equiv.Perm (Fin (w+b))) H,
      Eligible i (relabelSubgroup s H) ↔ Eligible i H) (i : Fin r) :
    ordinaryFirstOwnerPhysicalFamily U Eligible i =
      {H | H ∈ ordinaryFullOrbitPhysicalFamily (b := b) U ∧
        (¬ IsCriticalSubgroup (w+b) H ∧ FirstOwned Eligible i H)} :=
  fusionPhysicalFamily_filter U
    (finSumFinEquiv : Fin w ⊕ Fin b ≃ Fin (w+b))
    (fun H => H.map (MonoidHom.fst U (Equiv.Perm (Fin b)))=⊤)
    (fun H => ¬ IsCriticalSubgroup (w+b) H ∧ FirstOwned Eligible i H)
    (fun s H => ordinaryRemainder_firstOwned_relabel_iff (w+b) Eligible hEligible i s H)

/-- The filtered cover required by the finite-menu theorem follows from
ordinary full-action coverage of the same original first-owned subgroups.
The preservation of all filters is proved, not an extra coverage input. -/
theorem ordinaryFirstOwner_cover_of_fullOrbit_cover {w b r : ℕ}
    (U : Subgroup (Equiv.Perm (Fin w)))
    (Eligible : Fin r → Subgroup (Equiv.Perm (Fin (w+b))) → Prop)
    (hEligible : ∀ i (s : Equiv.Perm (Fin (w+b))) H,
      Eligible i (relabelSubgroup s H) ↔ Eligible i H) (i : Fin r)
    (hcover : ∀ H : Subgroup (Equiv.Perm (Fin (w+b))),
      ¬ IsCriticalSubgroup (w+b) H → FirstOwned Eligible i H →
        H ∈ ordinaryFullOrbitPhysicalFamily (b := b) U) :
    ∀ H : Subgroup (Equiv.Perm (Fin (w+b))),
      ¬ IsCriticalSubgroup (w+b) H → FirstOwned Eligible i H →
        H ∈ ordinaryFirstOwnerPhysicalFamily U Eligible i := by
  intro H hnoncritical howner
  rw [ordinaryFirstOwnerPhysicalFamily_eq_filter U Eligible hEligible i]
  exact ⟨hcover H hnoncritical howner,hnoncritical,howner⟩

/-- It suffices to identify an actual full U-action family for every
eligible physical subgroup, before testing any earlier exclusions. -/
theorem ordinaryFirstOwner_cover_of_eligible {w b r : ℕ}
    (U : Subgroup (Equiv.Perm (Fin w)))
    (Eligible : Fin r → Subgroup (Equiv.Perm (Fin (w+b))) → Prop)
    (hEligible : ∀ i (s : Equiv.Perm (Fin (w+b))) H,
      Eligible i (relabelSubgroup s H) ↔ Eligible i H) (i : Fin r)
    (hcover : ∀ H : Subgroup (Equiv.Perm (Fin (w+b))),
      Eligible i H → H ∈ ordinaryFullOrbitPhysicalFamily (b := b) U) :
    ∀ H : Subgroup (Equiv.Perm (Fin (w+b))),
      ¬ IsCriticalSubgroup (w+b) H → FirstOwned Eligible i H →
        H ∈ ordinaryFirstOwnerPhysicalFamily U Eligible i :=
  ordinaryFirstOwner_cover_of_fullOrbit_cover U Eligible hEligible i
    (fun H _ howner => hcover H howner.1)

/-- The comparison with an actual eligible orbit family is a literal
membership obligation. Local naturality alone does not prove this cover. -/
theorem ordinaryFirstOwner_card_le_physical {w b r : ℕ}
    (U : Subgroup (Equiv.Perm (Fin w)))
    (Eligible : Fin r → Subgroup (Equiv.Perm (Fin (w+b))) → Prop) (i : Fin r)
    (hcover : ∀ H : Subgroup (Equiv.Perm (Fin (w+b))),
      ¬ IsCriticalSubgroup (w+b) H → FirstOwned Eligible i H →
        H ∈ ordinaryFirstOwnerPhysicalFamily U Eligible i) :
    Nat.card {H : Subgroup (Equiv.Perm (Fin (w+b))) //
      ¬ IsCriticalSubgroup (w+b) H ∧ FirstOwned Eligible i H} ≤
      Nat.card (ordinaryFirstOwnerPhysicalFamily U Eligible i) := by
  let f : {H : Subgroup (Equiv.Perm (Fin (w+b))) //
      ¬ IsCriticalSubgroup (w+b) H ∧ FirstOwned Eligible i H} →
      ordinaryFirstOwnerPhysicalFamily U Eligible i :=
    fun H => ⟨H.1,hcover H.1 H.2.1 H.2.2⟩
  exact Nat.card_le_card_of_injective f
    (fun H K h => Subtype.ext
      (congrArg (fun L : ordinaryFirstOwnerPhysicalFamily U Eligible i => L.1) h))

/-- The first-owner family enters the original-action finite-menu bound
with naturality proved from physical conjugacy invariance. The original
normalizer, normal quotient, full source and all preceding exclusions remain.
Coverage, branch estimates, class counts and moments are not conclusions. -/
theorem binaryFiniteEntry_firstOwner_finite_menu {w b q₀ r : ℕ} {κ : Type*}
    (carriers : κ → CheckedPermutationCarrier w q₀)
    (U : Subgroup (Equiv.Perm (Fin w))) (hU : IsPGroup 2 U)
    (Eligible : Fin r → Subgroup (Equiv.Perm (Fin (w+b))) → Prop)
    (hEligible : ∀ i (s : Equiv.Perm (Fin (w+b))) H,
      Eligible i (relabelSubgroup s H) ↔ Eligible i H) (i : Fin r)
    (hcover : ∀ H : Subgroup (Equiv.Perm (Fin (w+b))),
      ¬ IsCriticalSubgroup (w+b) H → FirstOwned Eligible i H →
        H ∈ ordinaryFirstOwnerPhysicalFamily U Eligible i)
    (Φ : {N : Subgroup U // N.Normal} → Subgroup (Equiv.Perm (Fin b)) → ℝ)
    (D t M : {N : Subgroup U // N.Normal} → ℝ)
    (q : {N : Subgroup U // N.Normal} → ℕ)
    (hMaroti : NilpotentConjugacyClassInput)
    (hentries : ∀ N : {N : Subgroup U // N.Normal}, BinaryFiniteEntry carriers U N.1)
    (hD : ∀ N, 0≤D N) (ht : ∀ N, 0<t N) (hΦ : ∀ N J, 0≤Φ N J)
    (hpair : ∀ (N : {N : Subgroup U // N.Normal})
      (C : BinaryPhysicalPairCertificate U N.1),
      (C.localCertificate.coverDegree : ℝ)+2*Module.finrank (ZMod 2) C.physicalCut+
        4*representationSchurCapacity C.physicalRepresentation<w →
      ∀ J, fusionSurvivingEpiCount U (ordinaryFirstOwnerLocalPredicate U Eligible i) N J≤
        D N*Φ N J)
    (hcharacter : ∀ (N : {N : Subgroup U // N.Normal})
      (C : BinaryNormalCharacterCriterion (U ⧸ N.1) w) J,
      (Nat.card ((U ⧸ N.1) ≃* (U ⧸ N.1)) : ℝ)*
        (2 : ℝ)^(binaryCharacterSlope C.dimension*(b : ℝ))≤D N*Φ N J)
    (hcarrier : ∀ (N : {N : Subgroup U // N.Normal}) j,
      (carriers j).source=U → (carriers j).axis=N.1.map U.subtype →
      ∀ J, fusionSurvivingEpiCount U (ordinaryFirstOwnerLocalPredicate U Eligible i) N J≤
        D N*Φ N J)
    (hq : ∀ N, 1≤q N)
    (hmoment : ∀ N, (∑ J : Subgroup (Equiv.Perm (Fin b)), Φ N J^(q N))≤M N) :
    (Nat.card {H : Subgroup (Equiv.Perm (Fin (w+b))) //
      ¬ IsCriticalSubgroup (w+b) H ∧ FirstOwned Eligible i H} : ℝ)≤
      ((w+b).factorial : ℝ) /
        (b.factorial * (Nat.card (Subgroup.normalizer (U : Set (Equiv.Perm (Fin w)))) : ℝ)) *
      ∑ N : {N : Subgroup U // N.Normal},
        (D N/(t N)^(q N-1)*M N+(subgroupCount b : ℝ)*D N*t N) := by
  have hlocal := binaryFiniteEntry_finite_menu carriers U hU
    (ordinaryFirstOwnerLocalPredicate U Eligible i) Φ D hMaroti hentries
    (ordinaryFirstOwnerLocalPredicate_natural U Eligible hEligible i)
    t M q hD ht hΦ hpair hcharacter hcarrier hq hmoment
  have hcount := ordinaryFirstOwner_card_le_physical U Eligible i hcover
  rw [ordinaryFirstOwnerPhysicalFamily_card] at hcount
  have hcountReal :
      (Nat.card {H : Subgroup (Equiv.Perm (Fin (w+b))) //
        ¬ IsCriticalSubgroup (w+b) H ∧ FirstOwned Eligible i H} : ℝ) ≤
      (Nat.card (FusionOrbitFamily U (FusionAcceptedOrbitPredicate U
        (ordinaryFirstOwnerLocalPredicate U Eligible i))) : ℝ) := by
    exact_mod_cast hcount
  exact hcountReal.trans hlocal

end SymmetricSubgroupAsymptotics
