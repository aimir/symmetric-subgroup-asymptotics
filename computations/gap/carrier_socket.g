# Literal carrier ranks and Bockstein pullback controls.
# Input groups come from the pinned base alphabet; no catalogue is queried.

checks := 0;;
pullbacks := 0;;
markerPairs := 0;;

Check := function(flag, message)
  checks := checks + 1;
  if not flag then
    Error(Concatenation("CARRIER SOCKET: ", message));
  fi;
end;;

D2 := function(G)
  return LogInt(Size(G) / Size(FrattiniSubgroup(G)), 2);
end;;

Psi2 := function(G)
  local ph, generators;
  ph := FrattiniSubgroup(G);
  generators := Concatenation(
    List(GeneratorsOfGroup(ph), x -> x^2),
    GeneratorsOfGroup(CommutatorSubgroup(ph, G))
  );
  if Length(generators) = 0 then
    return TrivialSubgroup(G);
  fi;
  return Subgroup(G, generators);
end;;

Tau2 := function(G)
  return LogInt(Size(FrattiniSubgroup(G)) / Size(Psi2(G)), 2);
end;;

EllFromAbelianization := function(G)
  return Number(AbelianInvariants(G), x -> x mod 4 = 0);
end;;

C2 := CyclicGroup(IsPermGroup, 2);;
C4 := CyclicGroup(IsPermGroup, 4);;
q4 := GQuotients(C4, C2)[1];;

PowerProduct := function(G, e)
  return CallFuncList(DirectProduct, List([1..e], i -> G));
end;;

SameChar := function(A, f, g)
  return ForAll(GeneratorsOfGroup(A), x -> Image(f, x) = Image(g, x));
end;;

ZeroChar := function(A)
  local gens;
  gens := GeneratorsOfGroup(A);
  return GroupHomomorphismByImages(A, C2, gens,
    List(gens, x -> One(C2)));
end;;

CharProduct := function(A, f, g)
  local gens;
  gens := GeneratorsOfGroup(A);
  return GroupHomomorphismByImages(A, C2, gens,
    List(gens, x -> Image(f, x) * Image(g, x)));
end;;

UniqueChars := function(A, chars)
  local out, f;
  out := [];
  for f in chars do
    if not ForAny(out, g -> SameChar(A, f, g)) then
      Add(out, f);
    fi;
  od;
  return out;
end;;

CharSpan := function(A, rows)
  local span, f, additions;
  span := [ZeroChar(A)];
  for f in rows do
    additions := List(span, g -> CharProduct(A, g, f));
    Append(span, additions);
    span := UniqueChars(A, span);
  od;
  return span;
end;;

LiftableParities := function(A)
  local lifts, f, parity;
  lifts := [];
  for f in GQuotients(A, C4) do
    parity := CompositionMapping(q4, f);
    if not ForAny(lifts, g -> SameChar(A, parity, g)) then
      Add(lifts, parity);
    fi;
  od;
  return lifts;
end;;

IsLiftable := function(A, f, liftParities)
  if Size(Image(f)) = 1 then
    return true;
  fi;
  return ForAny(liftParities, g -> SameChar(A, f, g));
end;;

FirstNonLiftable := function(A, chars, liftParities)
  local f;
  for f in chars do
    if not IsLiftable(A, f, liftParities) then
      return f;
    fi;
  od;
  return fail;
end;;

FirstIndependent := function(A, f, chars)
  local g;
  for g in chars do
    if Length(CharSpan(A, [f,g])) = 4 then
      return g;
    fi;
  od;
  return fail;
end;;

FactorChar := function(A, factorMap, coordinate)
  local gens;
  gens := GeneratorsOfGroup(A);
  return GroupHomomorphismByImages(A, C2, gens,
    List(gens, x -> Image(factorMap, Image(Projection(A,coordinate), x))));
end;;

SourceMap := function(A, rows, V)
  local gens, e;
  gens := GeneratorsOfGroup(A);
  e := Length(rows);
  return GroupHomomorphismByImages(A, V, gens,
    List(gens, x -> Product(List([1..e], i ->
      Image(Embedding(V, i), Image(rows[i], x))))));
end;;

ParityMap := function(C4e, V, e)
  local gens;
  gens := GeneratorsOfGroup(C4e);
  return GroupHomomorphismByImages(C4e, V, gens,
    List(gens, x -> Product(List([1..e], i ->
      Image(Embedding(V, i),
            Image(q4, Image(Projection(C4e, i), x)))))));
end;;

PairMap := function(D, m1, m2)
  local C42, gens;
  C42 := DirectProduct(C4, C4);
  gens := GeneratorsOfGroup(D);
  return GroupHomomorphismByImages(D, C42, gens,
    List(gens, x ->
      Image(Embedding(C42, 1), Image(m1, x))
      * Image(Embedding(C42, 2), Image(m2, x))));
end;;

TestPullback := function(A, rows, label)
  local e, span, lifts, liftSpan, q, h, qp, V, C4e, src, parity,
        amb, pA, pC, gens, relation, H, K, phA, psA, phH, psH,
        i, j, ci, cj, pair, rowRank, expected;
  e := Length(rows);
  span := CharSpan(A, rows);
  lifts := LiftableParities(A);
  liftSpan := Filtered(span, f -> IsLiftable(A, f, lifts));
  q := LogInt(Length(span), 2);
  h := LogInt(Length(liftSpan), 2);
  qp := q - h;
  Check(Length(span) = 2^q, Concatenation(label, " row-span size"));
  Check(Length(liftSpan) = 2^h,
        Concatenation(label, " liftable intersection is a subspace"));
  Check(h <= Minimum(q, EllFromAbelianization(A)),
        Concatenation(label, " h bound"));

  V := PowerProduct(C2, e);
  C4e := PowerProduct(C4, e);
  src := SourceMap(A, rows, V);
  parity := ParityMap(C4e, V, e);
  Check(IsGroupHomomorphism(src), Concatenation(label, " source map"));
  Check(IsGroupHomomorphism(parity), Concatenation(label, " parity map"));
  Check(LogInt(Size(Image(src)), 2) = q,
        Concatenation(label, " ordinary map rank"));
  for i in [1..e] do
    Check(Size(Image(rows[i])) = 2,
          Concatenation(label, " nonzero component"));
  od;

  amb := DirectProduct(A, C4e);
  pA := Projection(amb, 1);
  pC := Projection(amb, 2);
  gens := GeneratorsOfGroup(amb);
  relation := GroupHomomorphismByImages(amb, V, gens,
    List(gens, x -> Image(src, Image(pA, x))
                    * Image(parity, Image(pC, x))^-1));
  Check(IsGroupHomomorphism(relation),
        Concatenation(label, " pullback relation"));
  H := Kernel(relation);
  K := Intersection(H, Image(Embedding(amb, 2)));
  phA := FrattiniSubgroup(A);
  psA := Psi2(A);
  phH := FrattiniSubgroup(H);
  psH := Psi2(H);

  Check(Size(H) = Size(A) * 2^e, Concatenation(label, " pullback order"));
  Check(Size(K) = 2^e, Concatenation(label, " central kernel order"));
  Check(IsElementaryAbelian(K), Concatenation(label, " kernel elementary"));
  Check(IsSubgroup(Centre(H), K), Concatenation(label, " kernel central"));
  Check(Size(Intersection(K, phH)) = 2^qp,
        Concatenation(label, " Bockstein image rank"));
  Check(Size(K) / Size(Intersection(K, phH)) = 2^(e-qp),
        Concatenation(label, " restriction rank"));
  Check(D2(H) = D2(A) + e - qp,
        Concatenation(label, " exact d formula"));
  Check(Tau2(H) <= Tau2(A) + qp,
        Concatenation(label, " tau upper formula"));
  Check(Size(Image(RestrictedMapping(pA, phH))) = Size(phA),
        Concatenation(label, " Phi onto"));
  Check(Size(Image(RestrictedMapping(pA, psH))) = Size(psA),
        Concatenation(label, " Psi onto"));
  Check(Size(phH) / Size(psH)
        = (Size(phA) / Size(psA))
          * Size(Intersection(K, phH)) / Size(Intersection(K, psH)),
        Concatenation(label, " exact Phi/Psi kernel sequence"));

  for i in [1..e] do
    ci := GroupHomomorphismByImages(amb, C4, gens,
      List(gens, x -> Image(Projection(C4e, i), Image(pC, x))));
    Check(Size(Image(RestrictedMapping(ci, H))) = 4,
          Concatenation(label, " displayed C4 full"));
    for j in [i+1..e] do
      cj := GroupHomomorphismByImages(amb, C4, gens,
        List(gens, x -> Image(Projection(C4e, j), Image(pC, x))));
      pair := PairMap(amb, ci, cj);
      rowRank := LogInt(Length(CharSpan(A, [rows[i], rows[j]])), 2);
      expected := 4 * 2^rowRank;
      Check(Size(Image(RestrictedMapping(pair, H))) = expected,
            Concatenation(label, " downstream pair order"));
      Check(expected = 8 or expected = 16,
            Concatenation(label, " downstream never graph-sized"));
    od;
  od;
  pullbacks := pullbacks + 1;
end;;

TestMarker := function(A, rows, label)
  local e, V, C4e, src, parity, D, gens, earlyRelation, lateRelation,
        J, axes, i, j, late, pair, pairSize, graphPairs;
  e := Length(rows);
  V := PowerProduct(C2, e);
  C4e := PowerProduct(C4, e);
  src := SourceMap(A, rows, V);
  parity := ParityMap(C4e, V, e);
  D := DirectProduct(C4, C4, A, C4e);
  gens := GeneratorsOfGroup(D);
  earlyRelation := GroupHomomorphismByImages(D, C4, gens,
    List(gens, x -> Image(Projection(D, 2), x)
                    * Image(Projection(D, 1), x)^-1));
  lateRelation := GroupHomomorphismByImages(D, V, gens,
    List(gens, x -> Image(src, Image(Projection(D, 3), x))
                    * Image(parity, Image(Projection(D, 4), x))^-1));
  Check(IsGroupHomomorphism(earlyRelation),
        Concatenation(label, " early graph relation"));
  Check(IsGroupHomomorphism(lateRelation),
        Concatenation(label, " late relation"));
  J := Intersection(Kernel(earlyRelation), Kernel(lateRelation));

  axes := [Projection(D, 1), Projection(D, 2)];
  for i in [1..e] do
    late := GroupHomomorphismByImages(D, C4, gens,
      List(gens, x -> Image(Projection(C4e, i),
                            Image(Projection(D, 4), x))));
    Add(axes, late);
  od;
  graphPairs := 0;
  for i in [1..Length(axes)-1] do
    for j in [i+1..Length(axes)] do
      pair := PairMap(D, axes[i], axes[j]);
      pairSize := Size(Image(RestrictedMapping(pair, J)));
      if pairSize = 4 then
        graphPairs := graphPairs + 1;
        Check(i = 1 and j = 2,
              Concatenation(label, " unique order-four pair location"));
      elif i <= 2 and j >= 3 then
        Check(pairSize = 16,
              Concatenation(label, " early/downstream independent"));
      else
        Check(pairSize = 8 or pairSize = 16,
              Concatenation(label, " dependent pair order eight"));
      fi;
      markerPairs := markerPairs + 1;
    od;
  od;
  Check(graphPairs = 1, Concatenation(label, " one graph-sized pair"));
end;;


# Fixed finite profile data, bound to the separately pinned literal alphabet.
Check(SocketData.schema_version=1,"socket schema");;
indices := List(SocketData.carriers,x->Int(SplitString(x.action_id,"T")[2]));;
degrees := List(SocketData.carriers,x->Int(SplitString(x.action_id,"T")[1]));;
Check(List(SocketData.carriers,x->x.action_id)=["8T18","8T26","8T27","8T28","8T29","8T31","8T35","16T1082","16T1083","16T1084","16T1332","16T1547"],"exact twelve-carrier domain");;
weights := List(SocketData.carriers,x->x.weight);;
abelian := List(SocketData.carriers,x->x.abelianization);;
ds := List(SocketData.carriers,x->x.d);;
ells := List(SocketData.carriers,x->x.ell);;
taus := List(SocketData.carriers,x->x.tau);;
normalizers := List(SocketData.carriers,x->x.normalizer_order);;
FEWCheckBaseAlphabet(SocketAlphabet.actions);;
carriers := [];;

for pos in [1..Length(indices)] do
  row := First(SocketAlphabet.actions,a->a.degree=degrees[pos] and a.catalogue_locator[2]=indices[pos]);
  Check(row<>fail and row.role="carrier","fixed original carrier action");
  G := FEWGroup(row.generators,row.degree);
  Check(weights[pos]=row.degree/8,"physical weight");
  Add(carriers, G);
  Check(Size(G) = row.order, "named carrier order");
  Check(AbelianInvariants(G) = abelian[pos], "named carrier abelianization");
  Check(D2(G) = ds[pos], "named carrier d");
  Check(EllFromAbelianization(G) = ells[pos], "named carrier ell");
  Check(Tau2(G) = taus[pos], "named carrier tau");
  Check(ds[pos] + ells[pos] <= 3 * weights[pos], "named d+ell inequality");
  Check(taus[pos] <= 2 * weights[pos], "named tau inequality");
  Check(4 * ds[pos] + 5 * ells[pos] >= 10 * weights[pos],
        "named branch inequality");
  ambient := SymmetricGroup(degrees[pos]);
  Check(Size(Normalizer(ambient, G)) = normalizers[pos],
        "named action normalizer");
  liftParities := LiftableParities(G);
  Check(Length(liftParities) = 2^ells[pos]-1,
        "literal liftable-character nullity");
  if degrees[pos] = 16 then
    Check(FrattiniSubgroup(G) = DerivedSubgroup(G),
          "H16 Phi equals derived");
  fi;
od;

Check(IsomorphismGroups(carriers[3],carriers[4]) <> fail,
      "8T27 and 8T28 abstract groups agree");
Check(not IsConjugate(SymmetricGroup(8),carriers[3],carriers[4]), "8T27 and 8T28 named actions differ");
Check(IsomorphismGroups(carriers[5],carriers[6]) <> fail,
      "8T29 and 8T31 abstract groups agree");
Check(not IsConjugate(SymmetricGroup(8),carriers[5],carriers[6]), "8T29 and 8T31 named actions differ");


# Every named carrier: liftable and nonliftable patterns when available,
# plus dependent rows.  This directly attacks replacing q' by q.
for pos in [1..Length(carriers)] do
  A := carriers[pos];
  chars := GQuotients(A, C2);
  lifts := LiftableParities(A);
  Check(Length(chars) = 2^D2(A)-1, "all nonzero binary characters");
  if ells[pos] = 1 then
    lf := lifts[1];
    nf := FirstNonLiftable(A, chars, lifts);
    lnf := CharProduct(A, lf, nf);
    TestPullback(A, [lf], Concatenation("liftable ", String(indices[pos])));
    TestPullback(A, [nf], Concatenation("nonliftable ", String(indices[pos])));
    TestPullback(A, [lf,lf], Concatenation("lift repeated ", String(indices[pos])));
    TestPullback(A, [lf,nf], Concatenation("mixed basis ", String(indices[pos])));
    TestPullback(A, [lf,nf,lnf], Concatenation("mixed dependent ", String(indices[pos])));
  else
    f := chars[1];
    g := FirstIndependent(A, f, chars);
    fg := CharProduct(A, f, g);
    TestPullback(A, [f], Concatenation("one row ", String(indices[pos])));
    TestPullback(A, [f,f], Concatenation("repeated row ", String(indices[pos])));
    TestPullback(A, [f,g], Concatenation("rank two ", String(indices[pos])));
    TestPullback(A, [f,g,fg], Concatenation("dependent rank two ", String(indices[pos])));
  fi;
od;


# Mixed products: Kunneth separation must prevent cancellation between
# factor Bocksteins.  Include both non-elementary carriers and one elementary
# carrier.  The exact proof is universal; these are hostile finite witnesses.
A27 := carriers[3];;
A28 := carriers[4];;
A18 := carriers[1];;

for pair in [[A27,A18],[A27,A28]] do
  A := DirectProduct(pair[1], pair[2]);
  lifts1 := LiftableParities(pair[1]);
  lifts2 := LiftableParities(pair[2]);
  chars1 := GQuotients(pair[1], C2);
  chars2 := GQuotients(pair[2], C2);
  lf1 := lifts1[1];
  nf1 := FirstNonLiftable(pair[1], chars1, lifts1);
  nf2 := FirstNonLiftable(pair[2], chars2, lifts2);
  lf := FactorChar(A, lf1, 1);
  nf := FactorChar(A, nf1, 1);
  other := FactorChar(A, nf2, 2);
  Check(EllFromAbelianization(A)
        = EllFromAbelianization(pair[1])+EllFromAbelianization(pair[2]),
        "mixed ell additive");
  Check(Tau2(A) = Tau2(pair[1])+Tau2(pair[2]), "mixed tau additive");
  TestPullback(A, [lf,nf,other,CharProduct(A,nf,other)],
               "mixed-factor Bockstein separation");
od;


# The literal early-pair marker against dependent order-eight pairs, once
# with a liftable row and once at the tight 16T1332 branch carrier.
A := carriers[3];
lifts := LiftableParities(A);
lf := lifts[1];
nf := FirstNonLiftable(A, GQuotients(A,C2), lifts);
TestMarker(A, [lf,lf,nf], "8T27 liftable marker");

A := carriers[11];
chars := GQuotients(A,C2);
f := chars[1];
g := FirstIndependent(A, f, chars);
TestMarker(A, [f,f,g], "16T1332 branch marker");

Print("PASS CARRIER SOCKET: ", checks,
      " exact assertions; ", pullbacks, " Bockstein pullbacks; ",
      markerPairs, " literal C4 marker pairs\n");

