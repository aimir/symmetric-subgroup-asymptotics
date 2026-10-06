import SymmetricSubgroupAsymptotics.TerminalContraction
import SymmetricSubgroupAsymptotics.Non2PreE7DerivedHeadBounds
import SymmetricSubgroupAsymptotics.PermutationPrimeGroupRank

/-!
# A common `O^2` source for ternary cyclic-dual targets

Let `F = O^2(J)` be the literal intersection of the normal subgroups of a
finite source `J` with binary quotient.  If `Q` has a normal ternary subgroup
`V = O^2(Q)`, then every epimorphism `J → Q` maps the same `F` onto `V`.
Moreover, if a normal subgroup of `J` has image in `V`, that image is already
obtained from its intersection with `F`: the remaining quotient is at once a
2-group and a 3-group.

These two facts supply the common-source and recovery hypotheses of
`DerivedHead.epi_card_le_characters`.  Thus one character of `V` whose
conjugates separate points, together with self-centrality of `V`, gives

`|Epi(J,Q)| ≤ |Hom(O^2(J), C3)| |Aut Q|`.

For `J ≤ S_b`, the uniform prime-rank theorem then bounds the first factor
by `3^(b/3)`.  This argument never counts the binary quotient maps separately;
all quotient actions are recovered from the one literal restriction label.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics

namespace BinaryResidual

variable {J Q : Type*} [Group J] [Group Q]

/-- A normal ternary subgroup with binary quotient is exactly the literal
binary residual.  This is the elementary coprime identification used for a
split `V ⋊ R`, but the statement does not require a chosen complement or a
splitting.
-/
theorem terminalTwoResidual_eq_of_ternary_normal_binary_quotient
    [Finite Q] (V : Subgroup Q) [V.Normal]
    (hV3 : IsPGroup 3 V) (hquot : IsPGroup 2 (Q ⧸ V)) :
    terminalTwoResidual Q = V := by
  apply le_antisymm
  · exact terminalTwoResidual_le Q V hquot
  · let F := terminalTwoResidual Q
    letI : F.Normal := inferInstance
    let P := V.map (QuotientGroup.mk' F)
    have hP3 : IsPGroup 3 P := hV3.map (QuotientGroup.mk' F)
    have hP2 : IsPGroup 2 P :=
      (terminalTwoResidual_quotient_binary Q).to_subgroup P
    have hdis : Disjoint P P :=
      IsPGroup.disjoint_of_ne 2 3 (by norm_num) P P hP2 hP3
    have hPbot : P = ⊥ := disjoint_self.mp hdis
    intro v hv
    have himage : QuotientGroup.mk' F v ∈ P := ⟨v, hv, rfl⟩
    have himageBot : QuotientGroup.mk' F v ∈ (⊥ : Subgroup (Q ⧸ F)) := by
      rw [← hPbot]
      exact himage
    apply (QuotientGroup.eq_one_iff v).mp
    simpa using himageBot

/-- An epimorphism carries the literal binary residual onto the target
binary residual.  This is the `O^2` analogue of `map_derivedSeries_eq`.
-/
theorem map_terminalTwoResidual_eq [Finite J] [Finite Q]
    (phi : J →* Q) (hphi : Function.Surjective phi) :
    (terminalTwoResidual J).map phi = terminalTwoResidual Q := by
  let F := terminalTwoResidual J
  letI : F.Normal := inferInstance
  let W := F.map phi
  haveI : W.Normal := Subgroup.Normal.map inferInstance phi hphi
  apply le_antisymm
  · apply le_iInf
    intro N
    have hquot : IsPGroup 2 (Q ⧸ N.1) := terminalBinaryKernel_quotient Q N
    have hker : F ≤ ((QuotientGroup.mk' N.1).comp phi).ker :=
      terminalTwoResidual_le_ker (T := J)
        ((QuotientGroup.mk' N.1).comp phi) hquot
    rintro q ⟨j, hj, rfl⟩
    have hjker := hker hj
    change QuotientGroup.mk' N.1 (phi j) = 1 at hjker
    exact (QuotientGroup.eq_one_iff (phi j)).mp hjker
  · have hquot : IsPGroup 2 (Q ⧸ W) := by
      intro x
      obtain ⟨q, rfl⟩ := QuotientGroup.mk'_surjective W x
      obtain ⟨j, rfl⟩ := hphi q
      obtain ⟨k, hk⟩ := terminalTwoResidual_quotient_binary J
        ((QuotientGroup.mk' F) j)
      refine ⟨k, ?_⟩
      rw [← map_pow]
      apply (QuotientGroup.eq_one_iff (phi j ^ (2 ^ k))).mpr
      have hjF : j ^ (2 ^ k) ∈ F := by
        apply (QuotientGroup.eq_one_iff (j ^ (2 ^ k))).mp
        simpa only [map_pow] using hk
      exact ⟨j ^ (2 ^ k), hjF, map_pow phi j (2 ^ k)⟩
    exact terminalTwoResidual_le Q W hquot

/-- If the image of a normal subgroup lies in a ternary subgroup, then it is
already the image of its intersection with the common binary residual.

The proof is the coprime recovery step which replaces the absorption lemma
used for a derived-series source.  The quotient of the image by the
intersection image is a quotient of a ternary group.  It is also a quotient
of a subgroup of `J / O^2(J)`, hence binary, so it is trivial.
-/
theorem normal_image_le_inf_residual_map [Finite J] [Finite Q]
    (phi : J →* Q) (hphi : Function.Surjective phi)
    (V : Subgroup Q) (hV3 : IsPGroup 3 V)
    (K : Subgroup J) (hK : K.Normal) (hKV : K.map phi ≤ V) :
    K.map phi ≤ (K ⊓ terminalTwoResidual J).map phi := by
  let F := terminalTwoResidual J
  let W := K.map phi
  let L := (K ⊓ F).map phi
  have hLW : L ≤ W := Subgroup.map_mono inf_le_left
  have hW3 : IsPGroup 3 W := hV3.to_le hKV
  letI : K.Normal := hK
  haveI : L.Normal := Subgroup.Normal.map inferInstance phi hphi
  let L' : Subgroup W := L.subgroupOf W
  haveI : L'.Normal := inferInstance
  have hquot3 : IsPGroup 3 (W ⧸ L') := hW3.to_quotient L'
  have hquot2 : IsPGroup 2 (W ⧸ L') := by
    intro x
    obtain ⟨w, rfl⟩ := QuotientGroup.mk'_surjective L' x
    obtain ⟨j, hjK, hjw⟩ := w.2
    obtain ⟨k, hk⟩ := terminalTwoResidual_quotient_binary J
      ((QuotientGroup.mk' F) j)
    refine ⟨k, ?_⟩
    rw [← map_pow]
    apply (QuotientGroup.eq_one_iff (w ^ (2 ^ k))).mpr
    change (w : Q) ^ (2 ^ k) ∈ L
    have hjF : j ^ (2 ^ k) ∈ F := by
      apply (QuotientGroup.eq_one_iff (j ^ (2 ^ k))).mp
      simpa only [map_pow] using hk
    refine ⟨j ^ (2 ^ k), ⟨K.pow_mem hjK _, hjF⟩, ?_⟩
    simpa only [map_pow] using congrArg (fun y : Q => y ^ (2 ^ k)) hjw
  have htop2 : IsPGroup 2 (⊤ : Subgroup (W ⧸ L')) :=
    hquot2.to_subgroup ⊤
  have htop3 : IsPGroup 3 (⊤ : Subgroup (W ⧸ L')) :=
    hquot3.to_subgroup ⊤
  have hdis : Disjoint (⊤ : Subgroup (W ⧸ L')) ⊤ :=
    IsPGroup.disjoint_of_ne 2 3 (by norm_num) ⊤ ⊤ htop2 htop3
  have htopbot : (⊤ : Subgroup (W ⧸ L')) = ⊥ := disjoint_self.mp hdis
  intro q hq
  let w : W := ⟨q, hq⟩
  have hwbot : QuotientGroup.mk' L' w ∈ (⊥ : Subgroup (W ⧸ L')) := by
    rw [← htopbot]
    exact Subgroup.mem_top _
  have hw1 : QuotientGroup.mk' L' w = 1 := by simpa using hwbot
  have hwL' : w ∈ L' := (QuotientGroup.eq_one_iff w).mp hw1
  exact hwL'

end BinaryResidual

namespace DerivedHead

/-- A finite target whose binary residual is a self-centralizing ternary
cyclic-dual layer.  Minimality or irreducibility is not required: the one
character is allowed to be cyclic on a reducible semisimple dual.
-/
structure BinaryResidualCyclicTarget
    (Q : Type*) [Group Q] (V : Subgroup Q) [V.Normal] where
  residual_eq : terminalTwoResidual Q = V
  ternary : IsPGroup 3 V
  character : V →* Multiplicative (ZMod 3)
  self_centralizing : ∀ q : Q, (∀ v ∈ V, q * v = v * q) → q ∈ V
  separating : ∀ v : V,
    (∀ q : Q, character (MulAut.conjNormal q v) = 1) → v = 1

namespace BinaryResidualCyclicTarget

variable {Q J : Type*} [Group Q] [Finite Q] [Group J]
  {V : Subgroup Q} [V.Normal]

/-- Build the target record directly from a normal ternary layer and a
binary quotient.  In particular the equality with `O^2(Q)` is a theorem,
not an application-specific assumption.
-/
def of_ternary_normal_binary_quotient
    (hV3 : IsPGroup 3 V) (hquot : IsPGroup 2 (Q ⧸ V))
    (character : V →* Multiplicative (ZMod 3))
    (self_centralizing : ∀ q : Q, (∀ v ∈ V, q * v = v * q) → q ∈ V)
    (separating : ∀ v : V,
      (∀ q : Q, character (MulAut.conjNormal q v) = 1) → v = 1) :
    BinaryResidualCyclicTarget Q V where
  residual_eq :=
    BinaryResidual.terminalTwoResidual_eq_of_ternary_normal_binary_quotient
      V hV3 hquot
  ternary := hV3
  character := character
  self_centralizing := self_centralizing
  separating := separating

/-- Every onto map uses the same literal source `O^2(J)` and maps it onto
the fixed ternary layer `V`.
-/
theorem residual_image [Finite J]
    (D : BinaryResidualCyclicTarget Q V)
    (phi : GroupEpimorphism J Q) :
    (terminalTwoResidual J).map phi.1 = V := by
  rw [BinaryResidual.map_terminalTwoResidual_eq phi.1 phi.2, D.residual_eq]

/-- The coprime residual recovery required by the common cyclic-dual kernel
label theorem.
-/
theorem residual_lift [Finite J]
    (D : BinaryResidualCyclicTarget Q V)
    (phi : GroupEpimorphism J Q)
    (K : Subgroup J) (hK : K.Normal) (hKV : K.map phi.1 ≤ V) :
    K.map phi.1 ≤ (K ⊓ terminalTwoResidual J).map phi.1 :=
  BinaryResidual.normal_image_le_inf_residual_map phi.1 phi.2 V D.ternary K hK hKV

/-- **Common-`O^2` cyclic-dual epimorphism count.**

There is no multiplier for possible binary quotient maps: faithfulness and
the cyclic dual character recover them from the common restriction label.
-/
theorem epi_card_le [Finite J]
    (D : BinaryResidualCyclicTarget Q V) :
    Nat.card (GroupEpimorphism J Q) ≤
      Nat.card (terminalTwoResidual J →* Multiplicative (ZMod 3)) *
        Nat.card (Q ≃* Q) :=
  epi_card_le_characters (terminalTwoResidual J) V
    D.character D.separating D.self_centralizing
    D.residual_image D.residual_lift

/-- For an actual permutation source, the common restriction label has the
uniform ternary rank budget `b/3`.
-/
theorem epi_card_le_permutationSource
    (D : BinaryResidualCyclicTarget Q V)
    {b : ℕ} (J : Subgroup (Equiv.Perm (Fin b))) :
    Nat.card (GroupEpimorphism J Q) ≤
      3 ^ (b / 3) * Nat.card (Q ≃* Q) := by
  have h := D.epi_card_le (J := J)
  rw [card_hom_zmod_eq 3] at h
  exact h.trans (Nat.mul_le_mul_right _
    (Nat.pow_le_pow_right (by norm_num)
      (primeRank_le_of_subgroup 3 J (terminalTwoResidual J))))

/-- Real-exponential form used by the fixed-degree additive owners.
-/
theorem epi_card_le_ternary
    (D : BinaryResidualCyclicTarget Q V)
    {b : ℕ} (J : Subgroup (Equiv.Perm (Fin b))) :
    (Nat.card (GroupEpimorphism J Q) : ℝ) ≤
      (Nat.card (Q ≃* Q) : ℝ) *
        (2 : ℝ) ^ ((Real.logb 2 3 / 3) * b) := by
  have h := D.epi_card_le_permutationSource J
  have hpow := pow_floor_div_le_rpow 3 b (by norm_num)
  calc
    (Nat.card (GroupEpimorphism J Q) : ℝ) ≤
        (((3 ^ (b / 3)) * Nat.card (Q ≃* Q) : ℕ) : ℝ) := by
      exact_mod_cast h
    _ = (Nat.card (Q ≃* Q) : ℝ) * (3 : ℝ) ^ (b / 3) := by
      push_cast
      ring
    _ ≤ (Nat.card (Q ≃* Q) : ℝ) *
        (2 : ℝ) ^ ((Real.logb 2 3 / 3) * b) :=
      mul_le_mul_of_nonneg_left hpow (Nat.cast_nonneg _)

/-- The manuscript's displayed coefficient follows from the corresponding
finite target automorphism estimate.  In the split affine applications that
estimate is obtained by conjugating complements (coprime `H¹ = 0`) and then
restricting an automorphism to the ternary layer.
-/
theorem epi_card_le_of_aut_le
    (D : BinaryResidualCyclicTarget Q V)
    {d b : ℕ} (J : Subgroup (Equiv.Perm (Fin b)))
    (hAut : Nat.card (Q ≃* Q) ≤
      Nat.card V * Nat.card ((Fin d → ZMod 3) ≃ₗ[ZMod 3] (Fin d → ZMod 3))) :
    Nat.card (GroupEpimorphism J Q) ≤
      Nat.card V * Nat.card ((Fin d → ZMod 3) ≃ₗ[ZMod 3] (Fin d → ZMod 3)) *
        3 ^ (b / 3) := by
  have h := D.epi_card_le_permutationSource J
  calc
    Nat.card (GroupEpimorphism J Q) ≤
        3 ^ (b / 3) * Nat.card (Q ≃* Q) := h
    _ ≤ 3 ^ (b / 3) *
        (Nat.card V * Nat.card ((Fin d → ZMod 3) ≃ₗ[ZMod 3] (Fin d → ZMod 3))) :=
      Nat.mul_le_mul_left _ hAut
    _ = Nat.card V *
        Nat.card ((Fin d → ZMod 3) ≃ₗ[ZMod 3] (Fin d → ZMod 3)) * 3 ^ (b / 3) := by
      ring

end BinaryResidualCyclicTarget
end DerivedHead
end SymmetricSubgroupAsymptotics

end
