# Bounded API regressions, not an action/normal completeness argument.
# Load finite_entry_witnesses.g and install the literal base alphabet/charts
# first. This control intentionally uses NormalSubgroups on five FIXTURES;
# the independent complete-menu coverage checker does not use that oracle.
FEWRunFocusedControls:=function()
 local fixtures,U,U2,N,N2,ctx,e,chart,p,q,cover,f,direct,entries,kinds,start;
 start:=Runtime();entries:=0;kinds:=rec(pair:=0,character:=0,direct:=0,transport:=0);
 fixtures:=Concatenation([Group((1,2,3,4,5,6,7,8))],List(FEWCharts,c->c.source));
 for U in fixtures do
   ctx:=FEWPrepare(U,LargestMovedPoint(U));
   for N in NormalSubgroups(U) do
     e:=FEWExport(ctx,N);
     # Rebuild the source and normal from the serialized permutation rows.
     U2:=FEWGroup(FEWRows(GeneratorsOfGroup(U),ctx.degree),ctx.degree);
     N2:=FEWGroup(e.normal_generators,ctx.degree);
     FEWRequire(FEWCheck(U2,N2,e),"fresh literal round trip");
     entries:=entries+1;kinds.(e.kind):=kinds.(e.kind)+1;
   od;
 od;
 # Each exceptional map must also work in a different literal labelling.
 for chart in FEWCharts do
   p:=(1,2);U:=chart.source^p;N:=Kernel(chart.alpha)^p;
   e:=FEWExport(FEWPrepare(U,chart.degree),N);
   FEWRequire(e.kind="transport" and FEWCheck(U,N,e),"conjugated actual transport axis");
 od;
 # The menu search need not select its direct-cover alternative on these
 # fixtures. Verify that interface separately on the actual C8 -> C4 map.
 U:=Group((1,2,3,4,5,6,7,8));N:=Group((1,5)(2,6)(3,7)(4,8));
 q:=NaturalHomomorphismByNormalSubgroup(U,N);cover:=FEWCover(Image(q));
 f:=CompositionMapping(cover.map,q);
 direct:=rec(kind:="direct",normal_generators:=FEWGens(N,8),normal_order:=Size(N),
   cover_degree:=cover.degree,cover_images:=FEWRows(List(GeneratorsOfGroup(U),g->Image(f,g)),cover.degree),gap:=8-cover.degree);
 FEWRequire(FEWCheck(U,N,direct),"literal direct-cover interface");
 Print("PASS FINITE ENTRY CONTROLS: ",entries," normal records and fresh literal round trips; ",
   kinds,"; four conjugated transport axes; direct-cover interface; CPU ms ",Runtime()-start,"\n");
 return true;
end;;
