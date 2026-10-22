import SymmetricSubgroupAsymptotics.CFSGTwistedDPairedTorusAction
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTranspose

/-! Negative terminal root conjugation follows by transposing the checked
positive identities and solving the actual conjugation equality. No
transpose automorphism of the original Serre model is assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTwistedDNegativeTorusAction
open CFSGOrthogonalDSerreMatrices CFSGTwistedDPairedRootImages
open CFSGTwistedDPairedTorusImages CFSGTwistedDPairedTorusAction
open CFSGOrthogonalDIndexTranspose CFSGOrthogonalDGenerationForkTorus

theorem torus_transpose (s : ℕ) (q : CFSG.PrimePower) (c : (q.Extension 2)ˣ) :
    transposeUnit (q.Extension 2) (s + 4) (pairedNaturalTorus s q c).val =
      (pairedNaturalTorus s q c).val := by
  apply Units.ext
  change ((pairedNaturalTorus s q c).val : Mat (q.Extension 2) (s + 4)).transpose = _
  rw [pairedNaturalTorus_val, Matrix.diagonal_transpose]

private theorem negative_of_positive {K G : Type*} [Field K] [Group G]
    (T : G) (P N : K → G) (τ : G → G)
    (hτmul : ∀ x y, τ (x * y) = τ y * τ x)
    (hτinv : ∀ x, τ x⁻¹ = (τ x)⁻¹) (hT : τ T = T)
    (hPN : ∀ a, τ (P a) = N a) (d : Kˣ)
    (hpos : ∀ a, T * P a * T⁻¹ = P ((d : K)^2 * a)) (a : K) :
    T * N a * T⁻¹ = N (((d : K)⁻¹)^2 * a) := by
  let b := ((d : K)⁻¹)^2 * a
  have hb : (d : K)^2 * b = a := by
    dsimp only [b]
    field_simp [Units.ne_zero d]
  have h := congrArg τ (hpos b)
  rw [hτmul, hτmul, hτinv, hT, hPN, hPN, hb] at h
  calc
    _ = T * (T⁻¹ * (N b * T)) * T⁻¹ := congrArg (fun x => T * x * T⁻¹) h.symm
    _ = N b := by group
    _ = _ := rfl

theorem pen_negative_conjugation (s : ℕ) (q : CFSG.PrimePower) (c : (q.Extension 2)ˣ)
    (a : q.Extension 2) :
    pairedNaturalTorus s q c * naturalRoot s q true (pen (s + 2)) a *
        (pairedNaturalTorus s q c)⁻¹ =
      naturalRoot s q true (pen (s + 2)) (((c : q.Extension 2)⁻¹)^2 * a) :=
by
  apply Subtype.ext
  exact negative_of_positive (pairedNaturalTorus s q c).val
    (fun b => rootTransvection (q.Extension 2) (s + 4) false (pen (s + 2)) b)
    (fun b => rootTransvection (q.Extension 2) (s + 4) true (pen (s + 2)) b)
    (transposeUnit (q.Extension 2) (s + 4))
    (transposeUnit_mul (q.Extension 2) (s + 4))
    (transposeUnit_inv (q.Extension 2) (s + 4)) (torus_transpose s q c)
    (fun b => transposeUnit_root (q.Extension 2) (s + 4) false (pen (s + 2)) b) c
    (fun b => congrArg Subtype.val (pen_conjugation s q c b)) a

theorem last_negative_conjugation (s : ℕ) (q : CFSG.PrimePower) (c : (q.Extension 2)ˣ)
    (a : q.Extension 2) :
    pairedNaturalTorus s q c * naturalRoot s q true (last (s + 2)) a *
        (pairedNaturalTorus s q c)⁻¹ =
      naturalRoot s q true (last (s + 2)) (((frobeniusUnit q c : q.Extension 2)⁻¹)^2 * a) :=
by
  apply Subtype.ext
  exact negative_of_positive (pairedNaturalTorus s q c).val
    (fun b => rootTransvection (q.Extension 2) (s + 4) false (last (s + 2)) b)
    (fun b => rootTransvection (q.Extension 2) (s + 4) true (last (s + 2)) b)
    (transposeUnit (q.Extension 2) (s + 4))
    (transposeUnit_mul (q.Extension 2) (s + 4))
    (transposeUnit_inv (q.Extension 2) (s + 4)) (torus_transpose s q c)
    (fun b => transposeUnit_root (q.Extension 2) (s + 4) false (last (s + 2)) b)
    (frobeniusUnit q c) (fun b => congrArg Subtype.val (last_conjugation s q c b)) a

theorem paired_negative_conjugation (s : ℕ) (q : CFSG.PrimePower) (c : (q.Extension 2)ˣ)
    (a : q.Extension 2) :
    pairedNaturalTorus s q c * pairedNaturalRoot s q true a *
        (pairedNaturalTorus s q c)⁻¹ =
      pairedNaturalRoot s q true (((c : q.Extension 2)⁻¹)^2 * a) := by
  have hpow : (((c : q.Extension 2)⁻¹)^2 * a)^q.order =
      ((frobeniusUnit q c : q.Extension 2)⁻¹)^2 * a^q.order := by
    rw [frobeniusUnit_val]
    have h := (CFSGSerreOrdinaryTwists.definingFieldAutomorphism q 2).map_mul
      (((c : q.Extension 2)⁻¹)^2) a
    rw [map_pow, map_inv₀] at h
    simpa only [CFSGSerreOrdinaryTwists.definingFieldAutomorphism_apply] using h
  change pairedNaturalTorus s q c *
      (naturalRoot s q true (pen (s + 2)) a *
        naturalRoot s q true (last (s + 2)) (a^q.order)) *
        (pairedNaturalTorus s q c)⁻¹ = _
  calc
    _ = (pairedNaturalTorus s q c * naturalRoot s q true (pen (s + 2)) a *
          (pairedNaturalTorus s q c)⁻¹) *
        (pairedNaturalTorus s q c * naturalRoot s q true (last (s + 2)) (a^q.order) *
          (pairedNaturalTorus s q c)⁻¹) := by group
    _ = _ := by
      rw [pen_negative_conjugation, last_negative_conjugation]
      exact congrArg (fun z : q.Extension 2 =>
        naturalRoot s q true (pen (s + 2)) (((c : q.Extension 2)⁻¹)^2 * a) *
          naturalRoot s q true (last (s + 2)) z) hpow.symm

end SymmetricSubgroupAsymptotics.CFSGTwistedDNegativeTorusAction
