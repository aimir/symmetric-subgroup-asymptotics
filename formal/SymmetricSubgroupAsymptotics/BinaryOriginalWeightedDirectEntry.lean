import SymmetricSubgroupAsymptotics.BinaryOrderSevenCharacterDirectFusion
import SymmetricSubgroupAsymptotics.BinaryPhysicalPairParameters
import SymmetricSubgroupAsymptotics.BinarySevenCharacterInstalled
import SymmetricSubgroupAsymptotics.FusionEpimorphismTransport

/-!
# A width-uniform original-weight direct entry

This is the common local interface already used separately by the small-pair
and degree-sixteen arguments.  It records the exact original action and
normal, an even strictly shorter continuation prefix, all same-source
moments, and the arbitrary-survival envelope on the complete exterior.

The selection theorems below turn a complete choice of such entries into the
existing forward physical recurrence and its contractive row.  They contain
no action-cover assertion; physical coverage remains a separate theorem.
-/

set_option autoImplicit false
noncomputable section
open Filter
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics

/-- One exact direct continuation entry on a literal original normal. -/
structure BinaryOriginalWeightedDirectEntry {h : ℕ}
    (U : Subgroup (Equiv.Perm (Fin (2*h))))
    (N : Subgroup U) [N.Normal] where
  prefixDegree : ℕ
  markerHalf : ℕ
  liftConstant : ℝ
  gapParameter : ℝ
  momentWeight : {b : ℕ} → Subgroup (Equiv.Perm (Fin b)) → ℝ
  prefix_eq_two_mul : prefixDegree = 2*markerHalf
  prefix_lt : prefixDegree < 2*h
  liftConstant_nonneg : 0 ≤ liftConstant
  gapParameter_pos : 0 < gapParameter
  moment_le : ∀ b q : ℕ,
    (∑ J : Subgroup (Equiv.Perm (Fin b)), momentWeight J^q) ≤
      (subgroupCount (b+q*prefixDegree) : ℝ)
  original_envelope : ∀ {b : ℕ}
    (P : Subgroup (U × Equiv.Perm (Fin b)) → Prop)
    (J : Subgroup (Equiv.Perm (Fin b))),
    fusionSurvivingEpiCount U P ⟨N,inferInstance⟩ J ≤
      fusionLocalFactor b h prefixDegree liftConstant gapParameter * momentWeight J

namespace BinaryOriginalWeightedDirectEntry

variable {h : ℕ} {U : Subgroup (Equiv.Perm (Fin (2*h)))}
    {N : Subgroup U} [N.Normal]

/-- Transport an original-weight entry through an arbitrary equivalence of
the two literal action groups.  Numerical data and all same-source moments
are unchanged.  For an arbitrary survival predicate on the target, enlarge
to the complete target epimorphism set, transport that finite set through the
induced quotient equivalence, and use the source entry with unrestricted
survival. -/
def transport {V : Subgroup (Equiv.Perm (Fin (2*h)))}
    {M : Subgroup V} [M.Normal]
    (e : U ≃* V) (hM : N.map e.toMonoidHom = M)
    (E : BinaryOriginalWeightedDirectEntry U N) :
    BinaryOriginalWeightedDirectEntry V M where
  prefixDegree := E.prefixDegree
  markerHalf := E.markerHalf
  liftConstant := E.liftConstant
  gapParameter := E.gapParameter
  momentWeight := fun {b} J => E.momentWeight J
  prefix_eq_two_mul := E.prefix_eq_two_mul
  prefix_lt := E.prefix_lt
  liftConstant_nonneg := E.liftConstant_nonneg
  gapParameter_pos := E.gapParameter_pos
  moment_le := E.moment_le
  original_envelope := by
    intro b P J
    let q : (U ⧸ N) ≃* (V ⧸ M) := QuotientGroup.congr N M e hM
    have hsubNat :
        Nat.card {beta : GroupEpimorphism J (V ⧸ M) //
          P (fusionFullGoursatEncode ⟨M,inferInstance⟩ J beta).1} ≤
          Nat.card (GroupEpimorphism J (V ⧸ M)) :=
      Nat.card_le_card_of_injective Subtype.val Subtype.val_injective
    have hquot :
        Nat.card (GroupEpimorphism J (U ⧸ N)) =
          Nat.card (GroupEpimorphism J (V ⧸ M)) :=
      fusionGroupEpimorphism_card_congr (MulEquiv.refl J) q
    calc
      fusionSurvivingEpiCount V P ⟨M,inferInstance⟩ J ≤
          (Nat.card (GroupEpimorphism J (V ⧸ M)) : ℝ) := by
        unfold fusionSurvivingEpiCount
        exact_mod_cast hsubNat
      _ = (Nat.card (GroupEpimorphism J (U ⧸ N)) : ℝ) := by
        exact_mod_cast hquot.symm
      _ ≤ fusionLocalFactor b h E.prefixDegree E.liftConstant E.gapParameter *
          E.momentWeight J := by
        let allEquiv : {beta : GroupEpimorphism J (U ⧸ N) // True} ≃
            GroupEpimorphism J (U ⧸ N) :=
          { toFun := Subtype.val
            invFun := fun beta => ⟨beta,trivial⟩
            left_inv := fun _ => rfl
            right_inv := fun _ => rfl }
        have hcard := Nat.card_congr allEquiv
        have htarget := E.original_envelope (fun _ => True) J
        unfold fusionSurvivingEpiCount at htarget
        change (Nat.card {beta : GroupEpimorphism J (U ⧸ N) // True} : ℝ) ≤ _
          at htarget
        rw [hcard] at htarget
        exact htarget

/-- A physical pair certificate enters the direct interface whenever its
selected top-cover degree is even. -/
def ofPair (hU : IsPGroup 2 U) (C : BinaryPhysicalPairCertificate U N)
    (heven : Even C.localCertificate.coverDegree) :
    BinaryOriginalWeightedDirectEntry U N := by
  have hcover := Nat.two_mul_div_two_of_even heven
  refine {
    prefixDegree := C.prefixDegree
    markerHalf := C.localCertificate.coverDegree/2 + C.localCertificate.cutDimension
    liftConstant := C.liftConstant
    gapParameter := C.gapParameter
    momentWeight := fun {b} J => C.momentWeight J
    prefix_eq_two_mul := ?_
    prefix_lt := ?_
    liftConstant_nonneg := C.liftConstant_nonneg
    gapParameter_pos := C.gapParameter_pos
    moment_le := C.prefixDegree_moment_le
    original_envelope := fun {b} P J =>
      C.original_survivingEpiCount_le_localFactor_ambient hU P J }
  · unfold BinaryPhysicalPairCertificate.prefixDegree
    omega
  · have hgap := C.certified_gap
    omega

/-- The installed seven-character alternative is a zero-prefix direct entry;
the actual binary permutation class theorem is discharged internally. -/
def ofOrderSevenCharacter (hh : 0 < h) (hU : IsPGroup 2 U)
    (C : BinaryOrderSevenCharacterCertificate U N) :
    BinaryOriginalWeightedDirectEntry U N where
  prefixDegree := C.prefixDegree
  markerHalf := C.markerHalf
  liftConstant := C.liftConstant
  gapParameter := C.gapParameter
  momentWeight := fun {b} J => C.momentWeight J
  prefix_eq_two_mul := C.prefixDegree_eq_two_mul
  prefix_lt := C.prefixDegree_lt (by omega)
  liftConstant_nonneg := C.liftConstant_nonneg
  gapParameter_pos := C.gapParameter_pos
  moment_le := C.moment_le
  original_envelope := fun {b} P J =>
    BinaryOrderSevenCharacterCertificate.original_envelope C
      BinarySevenCharacterInstalled.class_input hU P J

end BinaryOriginalWeightedDirectEntry

/-- One direct entry chosen for every literal original normal. -/
abbrev BinaryOriginalWeightedDirectSelection {h : ℕ}
    (U : Subgroup (Equiv.Perm (Fin (2*h)))) :=
  ∀ N : {N : Subgroup U // N.Normal}, BinaryOriginalWeightedDirectEntry U N.1

namespace BinaryOriginalWeightedDirectSelection

variable {h : ℕ} {U : Subgroup (Equiv.Perm (Fin (2*h)))}
    (C : BinaryOriginalWeightedDirectSelection U)

def prefixDegree (N : {N : Subgroup U // N.Normal}) : ℕ := (C N).prefixDegree
def markerHalf (N : {N : Subgroup U // N.Normal}) : ℕ := (C N).markerHalf
def liftConstant (N : {N : Subgroup U // N.Normal}) : ℝ := (C N).liftConstant
def gapParameter (N : {N : Subgroup U // N.Normal}) : ℝ := (C N).gapParameter
def momentWeight (N : {N : Subgroup U // N.Normal})
    {b : ℕ} (J : Subgroup (Equiv.Perm (Fin b))) : ℝ :=
  (C N).momentWeight J

/-- The exact shifted row attached to the complete selection. -/
def directRow (n m : ℕ) : ℝ :=
  fusionPhysicalDirectRow (fun _ : Unit => h) (fun _ : Unit => U)
    (fun _ N => C.prefixDegree N) (fun _ N => C.liftConstant N)
    (fun _ N => C.gapParameter N) n m

theorem directRow_nonneg (n m : ℕ) : 0 ≤ C.directRow n m :=
  fusionPhysicalDirectRow_nonneg (fun _ : Unit => h) (fun _ : Unit => U)
    _ _ _ (fun _ N => (C N).liftConstant_nonneg) n m

theorem directRow_forward {n m : ℕ} (hnm : n ≤ m) : C.directRow n m = 0 :=
  fusionPhysicalDirectRow_forward (fun _ : Unit => h) (fun _ : Unit => U)
    _ _ _ (fun _ N => (C N).prefix_lt) hnm

/-- Any normalizer-natural physical family covered by the fixed action gets
the exact original-weight forward recurrence. -/
theorem direct_recurrence (n : ℕ) (hn : 2*h ≤ n)
    (F : Set (Subgroup (Equiv.Perm (Fin n))))
    (P : Subgroup (U × Equiv.Perm (Fin (n-2*h))) → Prop)
    (hP : FusionOrbitNatural U P)
    (hcover : ∀ H ∈ F, H ∈ FusionCanonicalFamily U hn P) :
    (Nat.card F : ℝ)/exactBenchmark n ≤
      ∑ m ∈ Finset.range n, C.directRow n m *
        ((subgroupCount m : ℝ)/exactBenchmark m) := by
  apply fusionPhysicalUnion_direct_recurrence
    (fun _ : Unit => h) (fun _ : Unit => U) n (fun _ => hn) F
    (fun _ => P) (fun _ => hP) (fun H hH => ⟨(),hcover H hH⟩)
    (fun _ N => C.prefixDegree N) (fun _ N => C.liftConstant N)
    (fun _ N => C.gapParameter N) (fun _ N J => C.momentWeight N J)
  · intro _ N
    exact (C N).prefix_lt
  · intro _ N
    exact (C N).liftConstant_nonneg
  · intro _ N J
    exact (C N).original_envelope P J
  · intro _ N
    simpa only [momentWeight, prefixDegree, pow_one, one_mul] using
      (C N).moment_le (n-2*h) 1

/-- The complete selected row has a positive exponential rate. -/
theorem directRow_decay :
    ∃ A κ : ℝ, 0 < A ∧ 0 < κ ∧ ∀ᶠ n : ℕ in atTop,
      ∑ m ∈ Finset.range n, C.directRow n m ≤ A*(2:ℝ)^(-κ*(n:ℝ)) := by
  apply fusionFiniteDirectRow_decay
    (fun j : FusionPhysicalMenuAxis (fun _ : Unit => h) (fun _ : Unit => U) => h)
    (fun j => C.prefixDegree j.2) (fun j => C.markerHalf j.2)
    (fun j => C.liftConstant j.2)
    (fun j => fusionPhysicalMenuDivisor (fun _ : Unit => h) (fun _ : Unit => U) j.1)
    (fun j => C.gapParameter j.2)
  · intro j
    exact (C j.2).prefix_lt
  · intro j
    exact (C j.2).prefix_eq_two_mul
  · intro j
    exact (C j.2).liftConstant_nonneg
  · intro j
    exact fusionPhysicalMenuDivisor_pos (fun _ : Unit => h) (fun _ : Unit => U) j.1
  · intro j
    exact (C j.2).gapParameter_pos

theorem directRow_contractive :
    ∀ᶠ n : ℕ in atTop, ∑ m ∈ Finset.range n, C.directRow n m ≤ 1/2 := by
  apply fusionFiniteDirectRow_contractive
    (fun j : FusionPhysicalMenuAxis (fun _ : Unit => h) (fun _ : Unit => U) => h)
    (fun j => C.prefixDegree j.2) (fun j => C.markerHalf j.2)
    (fun j => C.liftConstant j.2)
    (fun j => fusionPhysicalMenuDivisor (fun _ : Unit => h) (fun _ : Unit => U) j.1)
    (fun j => C.gapParameter j.2)
  · intro j
    exact (C j.2).prefix_lt
  · intro j
    exact (C j.2).prefix_eq_two_mul
  · intro j
    exact (C j.2).liftConstant_nonneg
  · intro j
    exact fusionPhysicalMenuDivisor_pos (fun _ : Unit => h) (fun _ : Unit => U) j.1
  · intro j
    exact (C j.2).gapParameter_pos

end BinaryOriginalWeightedDirectSelection
end SymmetricSubgroupAsymptotics

end
