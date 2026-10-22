import SymmetricSubgroupAsymptotics.CFSGTwistedDPairedTorusAction
import SymmetricSubgroupAsymptotics.CFSGTwistedDPairedRootAdditivity
import SymmetricSubgroupAsymptotics.CFSGTypeAPrimitiveUnitSquare

/-! Every natural paired positive root is the image of an explicit
commutator in the ORIGINAL fixed group. This proves membership in the
same original derived action image, not just in the whole fixed image. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped commutatorElement
namespace SymmetricSubgroupAsymptotics.CFSGTwistedDDerivedPairedRoots
open CFSG.Models.Chevalley CFSGSerreFixedRootElements CFSGTwistedDFixedA2
open CFSGOrthogonalDSerreMatrices CFSGTwistedDFixedCentralCocycle
open CFSGTwistedDPairedFixedRoots CFSGTwistedDPairedRootImages
open CFSGTwistedDPairedTorusWords CFSGTwistedDPairedTorusImages
open CFSGTwistedDPairedTorusAction CFSGTwistedDPairedRootAdditivity

private theorem rank_ge_four (s : ℕ) : 4 ≤ s + 4 := by omega

def derivedImageAction (s : ℕ) (q : CFSG.PrimePower) :=
  (fixedImageAction s q).comp (commutator (Fixed s q)).subtype

def naturalDerivedPreimage (s : ℕ) (q : CFSG.PrimePower) :
    Subgroup (elementaryRootGroup (q.Extension 2) (s + 4)) :=
  (derivedImageAction s q).range.comap
    (elementaryImageAction (q.Extension 2) (s + 4) (rank_ge_four s))

def pairedDerivedWord (s : ℕ) (q : CFSG.PrimePower) (c : (q.Extension 2)ˣ)
    (a : q.Extension 2) : Derived s q :=
  derivedCommutator (CartanMatrix.D (s + 4)) (q.Extension 2) CFSG.Models.dTwist
    (fun _ => q.order) (pairedTorus s q c) (pairedFork s q false a)

theorem derivedImageAction_apply (s : ℕ) (q : CFSG.PrimePower) (g : Derived s q) :
    derivedImageAction s q g = fixedImageAction s q g.val := rfl

theorem pairedDerivedWord_coe (s : ℕ) (q : CFSG.PrimePower) (c : (q.Extension 2)ˣ)
    (a : q.Extension 2) :
    (pairedDerivedWord s q c a).val = ⁅pairedTorus s q c, pairedFork s q false a⁆ := rfl

theorem natural_commutator (s : ℕ) (q : CFSG.PrimePower) (c : (q.Extension 2)ˣ)
    (a : q.Extension 2) :
    ⁅pairedNaturalTorus s q c, pairedNaturalRoot s q false a⁆ =
      pairedNaturalRoot s q false (((c : q.Extension 2)^2 - 1) * a) := by
  rw [commutatorElement_def, paired_conjugation, pairedNaturalRoot_inv,
    ← pairedNaturalRoot_add]
  congr 1
  ring

set_option maxRecDepth 4096 in
theorem pairedDerivedWord_image (s : ℕ) (q : CFSG.PrimePower) (c : (q.Extension 2)ˣ)
    (a : q.Extension 2) :
    derivedImageAction s q (pairedDerivedWord s q c a) =
      elementaryImageAction (q.Extension 2) (s + 4) (rank_ge_four s)
        (pairedNaturalRoot s q false (((c : q.Extension 2)^2 - 1) * a)) := by
  let μ := fixedImageAction s q
  let ν : elementaryRootGroup (q.Extension 2) (s + 4) →*
      ((orthogonalBaseChange (q.Extension 2) (s + 4) (rank_ge_four s)).range ≃ₗ[q.Extension 2]
        (orthogonalBaseChange (q.Extension 2) (s + 4) (rank_ge_four s)).range) :=
    elementaryImageAction (q.Extension 2) (s + 4) (rank_ge_four s)
  rw [derivedImageAction_apply, pairedDerivedWord_coe]
  calc
    _ = ⁅μ (pairedTorus s q c), μ (pairedFork s q false a)⁆ :=
      map_commutatorElement μ _ _
    _ = ⁅ν (pairedNaturalTorus s q c), ν (pairedNaturalRoot s q false a)⁆ := by
      rw [pairedTorus_image, paired_image]
      rfl
    _ = ν ⁅pairedNaturalTorus s q c, pairedNaturalRoot s q false a⁆ :=
      (map_commutatorElement ν _ _).symm
    _ = _ := congrArg ν (natural_commutator s q c a)

theorem exists_torus_parameter (q : CFSG.PrimePower) :
    ∃ c : (q.Extension 2)ˣ, (c : q.Extension 2)^2 ≠ 1 := by
  obtain ⟨c, hc⟩ := IsCyclic.exists_generator (α := (q.Extension 2)ˣ)
  refine ⟨c, CFSGTypeAPrimitiveUnitSquare.square_ne_one ?_ c hc⟩
  rw [CFSGTwistedANaturalMatrices.extension_two_card]
  have hq : 2 ≤ q.order := q.prime_isPrime.two_le.trans
    (Nat.le_self_pow (Nat.ne_of_gt q.exponent_pos) q.prime)
  nlinarith

theorem paired_mem_derived_preimage (s : ℕ) (q : CFSG.PrimePower) (t : q.Extension 2) :
    pairedNaturalRoot s q false t ∈ naturalDerivedPreimage s q := by
  obtain ⟨c, hc⟩ := exists_torus_parameter q
  have hd : (c : q.Extension 2)^2 - 1 ≠ 0 := sub_ne_zero.mpr hc
  let a := t / ((c : q.Extension 2)^2 - 1)
  have ha : ((c : q.Extension 2)^2 - 1) * a = t := by
    dsimp only [a]
    field_simp [hd]
  refine ⟨pairedDerivedWord s q c a, ?_⟩
  simpa only [ha] using pairedDerivedWord_image s q c a

end SymmetricSubgroupAsymptotics.CFSGTwistedDDerivedPairedRoots
