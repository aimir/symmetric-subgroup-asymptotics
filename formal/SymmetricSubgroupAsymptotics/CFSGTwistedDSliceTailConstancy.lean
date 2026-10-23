import SymmetricSubgroupAsymptotics.CFSGTwistedDSliceEdgeConstancy
import SymmetricSubgroupAsymptotics.CFSGHyperbolicNonzeroLevelConnected

/-! Connectivity now proves actual anisotropic image-tail constancy
on every nonzero norm slice. Every intermediate normalized image is
constructed from the actual point permutation; no slice-transitivity
or constancy premise is supplied. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTwistedDSliceTailConstancy
open CFSGTwistedDFixedQuadraticSpace CFSGTwistedDHyperbolicCoordinates
open CFSGTwistedDAnisotropicNormForm CFSGTwistedDSliceCoordinates
open CFSGTwistedDNormalizedSliceImages CFSGTwistedDSliceEdgeConstancy CFSGTwistedA2FixedField
open CFSGOrthogonalDIndexQuadraticSubspacePoints CFSGSingularPlaneTriangle

local instance (n : ℕ) (q : CFSG.PrimePower) :
    Module.Finite (fixedField q) (fixedSpace n q) := Module.Finite.of_finite

theorem normalized_image_norm (n : ℕ) (q : CFSG.PrimePower)
    (f : Points (fixedQuadraticForm n q) ≃ Points (fixedQuadraticForm n q))
    (a : q.Extension 2) (ha : a ≠ 0)
    (h : (Fin (n + 1) → fixedField q) × (Fin (n + 1) → fixedField q))
    (hh : dotProduct h.1 h.2 = -normForm q a) (b : q.Extension 2)
    (hb : NormalizedImage n q f a ha h hh b) : normForm q b = normForm q a := by
  let P := slicePoint n q a ha h hh
  have hv : sliceVector n q h b ∈ (f P).val := by
    rw [show (f P).val = Submodule.span (fixedField q) {sliceVector n q h b} from hb]
    exact Submodule.mem_span_singleton_self _
  have hQ := (f P).property.2 (sliceVector n q h b) hv
  rw [quadratic_sliceVector, hh] at hQ
  apply sub_eq_zero.mp
  calc
    normForm q b - normForm q a = -normForm q a + normForm q b := by ring
    _ = 0 := hQ

theorem normalized_image_tail_constant (n : ℕ) (q : CFSG.PrimePower) (hn : 1 ≤ n)
    (f : Points (fixedQuadraticForm n q) ≃ Points (fixedQuadraticForm n q))
    (horth : ∀ P R, ZeroOn (fixedQuadraticForm n q).polarBilin (f P).val (f R).val ↔
      ZeroOn (fixedQuadraticForm n q).polarBilin P.val R.val)
    (hfix : ∀ P : Points (fixedQuadraticForm n q),
      (∀ v ∈ P.val, anisotropicPart n q v = 0) → f P = P)
    (hlinear : ∀ W : Subspaces (fixedQuadraticForm n q),
      Nonempty (SemilinearPiece (fixedQuadraticForm n q) f W (RingEquiv.refl (fixedField q))))
    (a : q.Extension 2) (ha : a ≠ 0)
    (h k : (Fin (n + 1) → fixedField q) × (Fin (n + 1) → fixedField q))
    (hh : dotProduct h.1 h.2 = -normForm q a)
    (hk : dotProduct k.1 k.2 = -normForm q a)
    (b c : q.Extension 2)
    (hb : NormalizedImage n q f a ha h hh b)
    (hc : NormalizedImage n q f a ha k hk c) : b = c := by
  let t := -normForm q a
  have ht : t ≠ 0 := neg_ne_zero.mpr (normForm_ne_zero q ha)
  have hpath := CFSGHyperbolicNonzeroLevelConnected.connected
    (by simp only [Fintype.card_fin]; omega : 2 ≤ Fintype.card (Fin (n + 1))) t ht h k hh hk
  have hall : ∀ k, Relation.ReflTransGen (CFSGHyperbolicNonzeroLevelConnected.Step t) h k →
      ∀ (hk : dotProduct k.1 k.2 = -normForm q a) (b c : q.Extension 2),
        NormalizedImage n q f a ha h hh b → NormalizedImage n q f a ha k hk c → b = c := by
    intro k hp
    induction hp with
    | refl =>
      intro hk b c hb hc
      exact normalized_image_unique n q f a ha h hh b c hb hc
    | @tail k l path hstep ih =>
      intro hl b c hb hc
      have hk : dotProduct k.1 k.2 = -normForm q a := hstep.1
      have hd : dotProduct (k.1 - l.1) (k.2 - l.2) = 0 := hstep.2.2
      obtain ⟨e, he⟩ := exists_normalized_image n q hn f horth hfix a ha k hk
      exact (ih hk b e hb he).trans
        (normalized_image_eq_of_edge n q f hfix hlinear a ha k l hk hl hd e c he hc)
  exact hall k hpath hk b c hb hc

theorem exists_common_slice_tail (n : ℕ) (q : CFSG.PrimePower) (hn : 1 ≤ n)
    (f : Points (fixedQuadraticForm n q) ≃ Points (fixedQuadraticForm n q))
    (horth : ∀ P R, ZeroOn (fixedQuadraticForm n q).polarBilin (f P).val (f R).val ↔
      ZeroOn (fixedQuadraticForm n q).polarBilin P.val R.val)
    (hfix : ∀ P : Points (fixedQuadraticForm n q),
      (∀ v ∈ P.val, anisotropicPart n q v = 0) → f P = P)
    (hlinear : ∀ W : Subspaces (fixedQuadraticForm n q),
      Nonempty (SemilinearPiece (fixedQuadraticForm n q) f W (RingEquiv.refl (fixedField q))))
    (a : q.Extension 2) (ha : a ≠ 0) :
    ∃ b : q.Extension 2, normForm q b = normForm q a ∧
      ∀ (h : (Fin (n + 1) → fixedField q) × (Fin (n + 1) → fixedField q))
        (hh : dotProduct h.1 h.2 = -normForm q a), NormalizedImage n q f a ha h hh b := by
  let h : (Fin (n + 1) → fixedField q) × (Fin (n + 1) → fixedField q) :=
    (Pi.single 0 1, Pi.single 0 (-normForm q a))
  have hh : dotProduct h.1 h.2 = -normForm q a := by
    simp only [h, single_dotProduct, Pi.single_eq_same, one_mul]
  obtain ⟨b, hb⟩ := exists_normalized_image n q hn f horth hfix a ha h hh
  refine ⟨b, normalized_image_norm n q f a ha h hh b hb, ?_⟩
  intro k hk
  obtain ⟨c, hc⟩ := exists_normalized_image n q hn f horth hfix a ha k hk
  have he := normalized_image_tail_constant n q hn f horth hfix hlinear a ha h k hh hk b c hb hc
  rw [← he] at hc
  exact hc

end SymmetricSubgroupAsymptotics.CFSGTwistedDSliceTailConstancy
