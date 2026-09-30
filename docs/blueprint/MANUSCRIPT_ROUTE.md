# Reading the manuscript

The main theorem counts actual subgroups of `S_n`, with exponential relative
error against the exact coefficient benchmark in [SPEC.md](../../SPEC.md).
The [LaTeX manuscript](../../paper/main.tex) supplies the proofs. Its external
mathematical and computational inputs are listed in
[ASSUMPTIONS.md](../../ASSUMPTIONS.md).

## Proof structure

1. **Critical family and exact fibres.** The critical actions determine the
   exponential generating function. The central-lift argument counts every
   subgroup with those projections, including noncanonical lifts. The terminal
   and small-support lemmas bound the remaining complete fibres.
2. **Reusable counting estimates.** Section capacity retains the restriction
   annihilator. Quotient moments use the same complete complementary group.
   Fixed and growing quotient covers preserve the original action normalizer,
   the occurrence factorial and the one terminal attachment. Character and
   chief-layer estimates supply the concrete fibre bounds.
3. **Nonbinary action exhaustion.** Primitive and minimal-block reductions,
   followed by the bounded affine, ternary and pair-count arguments, prove
   that every action outside the binary/natural-C3/A4/S3/fixed alphabet has
   a complete negligible scalar or a contractive forward row. This is the
   theorem in [nonbinary_alphabet.tex](../../paper/sections/nonbinary_alphabet.tex).
   The bounded zero-ternary cases use the
   [literal induced-frame package](../../computations/frames/README.md).
4. **Ordinary-target binary recurrence.** The degree-32 boundary, unbounded
   widths, complete finite entry menu, normalizer-saturated degree-16 direct
   entries, and critical/C4/carrier mixture are combined in
   [binary_complete.tex](../../paper/sections/binary_complete.tex). The result
   bounds the complete binary error `E_N` by an exponentially small scalar
   plus an exponentially small row of complete ordinary counts `A_m`, with
   `m<2N`. No bounded ordinary subgroup ratio is used to prove the row.
   The [original-orbit recurrence](../../paper/sections/binary_original_fusion.tex)
   records a parallel generic width-at-least-32 statement, using a central cut
   or the original quotient character bound. Its row has the same complete
   ordinary targets and can be inserted directly into the ordinary master
   when used. Neither route creates a separate induction that first closes
   the complete binary count.
5. **First c=1 application and audits.** The exact surviving-character formula,
   earlier complete source estimates and relative ternary ranks prove the
   split c=1 application. The shared-C3 moment and inverse-complement chart
   check the same-source and multiplicity requirements. This application
   is separately proved, rather than inferred from a final asymptotic.
6. **Remaining packets and markers.** In the residual alphabet, the relative
   ternary predicate needed by the small natural C3/A4 packet theorem holds
   intrinsically. The small and macroscopic packet estimates remove every
   positive packet. Marker collapse then has only complete binary-error
   sources, with one even term and the exact two odd terms. The binary
   recurrence is applied to those terms immediately, producing a strictly
   forward ordinary row before the global induction.
7. **Boundedness and asymptotics.**
   [assembly.tex](../../paper/sections/assembly.tex) proves the exhaustive
   ordinary counting inequality. Its one ordinary-target recurrence first
   establishes boundedness and then obtains exponential convergence. The
   analytic section evaluates the exact
   benchmark by a positive saddle and gives the elementary four-periodic
   expansion and its first correction.

## Finite inputs

The [certificate inventory](../../certificates/README.md) states each finite
scope and its coverage argument. Group classifications, literal witness
acceptance, module-lattice completeness and the infinite counting implications
are distinct inputs. The manuscript proves the implications explicitly.
The extra affine-nine and narrow socket datasets give independent local
checks; the main proof uses general frame and mixture bounds on those domains.

The earlier component blueprint pages provide reusable mathematical interfaces.
The ordered argument above is the route used by the manuscript. In particular,
the final partition does not require an additional regular-orbit or endpoint
case split after the complete nonbinary action theorem.
