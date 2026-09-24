# Literal degree-16 nonbinary character, quotient-map, and normal-list certificates.
# Discovery may use NormalSubgroups; verification uses class-normal-closure joins.
NBChecks:=0;;
NonbinaryAlphabet:=fail;;
NBRequire:=function(ok,msg)
  NBChecks:=NBChecks+1;
  if not ok then Error(Concatenation("NONBINARY: ",msg));fi;
end;;
NBGroup:=function(rows)
  if Length(rows)=0 then return Group(());fi;
  return Group(List(rows,PermList));
end;;
NBPerms:=function(gs,w)return List(gs,g->List([1..w],i->i^g));end;;
NBJSON:=fail;;
NBJSON:=function(v)
  local ks;
  if IsInt(v) then return String(v);fi;
  if IsStringRep(v) then return Concatenation("\"",v,"\"");fi;
  if IsList(v) then return Concatenation("[",JoinStringsWithSeparator(List(v,NBJSON),","),"]");fi;
  if IsRecord(v) then ks:=SortedList(RecNames(v));return Concatenation("{",JoinStringsWithSeparator(List(ks,k->Concatenation(NBJSON(k),":",NBJSON(v.(k)))),","),"}");fi;
  Error("unsupported nonbinary JSON value");
end;;
NBCyclo:=function(x)
  local n;
  if IsInt(x) then return x;fi;
  n:=Conductor(x);
  return rec(conductor:=n,coefficients:=List(CoeffsCyc(x,n),a->[NumeratorRat(a),DenominatorRat(a)]));
end;;
NBValue:=function(x)
  if IsInt(x) then return x;fi;
  return Sum([1..x.conductor],i->x.coefficients[i][1]/x.coefficients[i][2]*E(x.conductor)^(i-1));
end;;
NBModel:=function(kind,d)
  local shift,gens,j;
  shift:=function(g,j)local p,k;p:=[1..4*d];for k in [1..4] do p[4*j+k]:=4*j+k^g;od;return PermList(p);end;
  gens:=Concatenation(List([0..d-1],j->[shift((1,2)(3,4),j),shift((1,3)(2,4),j)]));
  Add(gens,Product(List([0..d-1],j->shift((1,2,3),j))));
  if kind="S" then Add(gens,Product(List([0..d-1],j->shift((1,2),j))));fi;
  return Group(gens);
end;;
NBComparator:=function()return Group((1,2),(3,4),(5,6),(7,8));end;;

# Find a least-cost fixed irreducible tuple, retaining literal kernel indices.
NBPaths:=function(U,ns,irr)
  local ks,meet,best,paths,queue,cur,j,k,z,cost;
  ks:=List(irr,x->Position(ns,KernelOfCharacter(x)));
  meet:=List(ns,N->List(ks,k->Position(ns,Intersection(N,ns[k]))));
  best:=List(ns,x->10^100);paths:=List(ns,x->[]);
  j:=Position(ns,U);best[j]:=1;queue:=[[1,j]];
  while Length(queue)>0 do
    Sort(queue);cur:=Remove(queue,1);j:=cur[2];
    if cur[1]<>best[j] then continue;fi;
    for k in [1..Length(irr)] do
      if DegreeOfCharacter(irr[k])=1 then cost:=3;else cost:=5;fi;
      z:=meet[j][k];cost:=cost*cur[1];
      if cost<best[z] then best[z]:=cost;paths[z]:=Concatenation(paths[j],[k]);Add(queue,[cost,z]);fi;
    od;
  od;
  return rec(costs:=best,paths:=paths,kernels:=ks);
end;;

NBProduceAction:=function(a)
  local U,ns,classes,irr,paths,atoms,classrows,entries,chars,used,j,N,k,cert,
    phi,Q,Z,C,psi,R,model,kind,d,iso,hom,E,cmp,normalizer,joins,record;
  U:=NBGroup(a.generators);ns:=ShallowCopy(NormalSubgroups(U));SortBy(ns,Size);
  NBRequire(Length(ns)=a.normal_count,"producer normal count");
  classes:=ConjugacyClasses(U);irr:=Irr(U);
  NBRequire(ConjugacyClasses(CharacterTable(U))=classes,"character class alignment");
  paths:=NBPaths(U,ns,irr);
  classrows:=List(classes,c->rec(representative:=NBPerms([Representative(c)],a.degree)[1],
    size:=Size(c),normal_closure:=Position(ns,NormalClosure(U,Group(Representative(c))))));
  atoms:=Set(List(classrows,c->c.normal_closure));
  E:=DerivedSubgroup(U);cmp:=fail;
  if a.family="comparator" then
    phi:=NaturalHomomorphismByNormalSubgroup(U,E);iso:=IsomorphismGroups(Image(phi),NBComparator());
    NBRequire(iso<>fail,"comparator exists");hom:=CompositionMapping(iso,phi);
    cmp:=rec(kernel:=Position(ns,E),generator_images:=NBPerms(List(GeneratorsOfGroup(U),g->Image(hom,g)),8));
  fi;
  entries:=[];used:=[];
  for j in [1..Length(ns)] do
    N:=ns[j];
    if a.family="comparator" and IsSubgroup(N,E) then
      cert:=rec(kind:="comparator");
    elif paths.costs[j]^64<=2^(24*a.degree-3) then
      cert:=rec(kind:="mixed",linear:=Filtered(paths.paths[j],k->DegreeOfCharacter(irr[k])=1),
        general:=Filtered(paths.paths[j],k->DegreeOfCharacter(irr[k])<>1));
      used:=Union(used,paths.paths[j]);
    else
      NBRequire(a.family="head","uncovered normal kernel");
      phi:=NaturalHomomorphismByNormalSubgroup(U,N);Q:=Image(phi);Z:=Centre(Q);C:=PreImage(phi,Z);
      NBRequire(IsElementaryAbelian(Z) and Size(Z)=2^LogInt(Size(Z),2),"elementary central head");
      psi:=NaturalHomomorphismByNormalSubgroup(U,C);R:=Image(psi);model:=fail;
      for d in [1..3] do for kind in ["A","S"] do
        if Size(R)=Size(NBModel(kind,d)) then
          iso:=IsomorphismGroups(R,NBModel(kind,d));
          if iso<>fail then model:=[kind,d,iso];break;fi;
        fi;
      od;if model<>fail then break;fi;od;
      NBRequire(model<>fail,"repeated head quotient exists");hom:=CompositionMapping(model[3],psi);
      cert:=rec(kind:="head",central_preimage:=Position(ns,C),central_rank:=LogInt(Size(Z),2),
        model_type:=model[1],model_rank:=model[2],
        generator_images:=NBPerms(List(GeneratorsOfGroup(U),g->Image(hom,g)),4*model[2]));
    fi;
    joins:=List(atoms,k->Position(ns,ClosureGroup(N,ns[k])));
    Add(entries,rec(generators:=NBPerms(SmallGeneratingSet(N),a.degree),order:=Size(N),joins:=joins,certificate:=cert));
  od;
  chars:=List(used,k->rec(degree:=DegreeOfCharacter(irr[k]),kernel:=paths.kernels[k],
    values:=List(ValuesOfClassFunction(irr[k]),NBCyclo)));
  for N in entries do
    if N.certificate.kind="mixed" then
      N.certificate.linear:=List(N.certificate.linear,k->Position(used,k));
      N.certificate.general:=List(N.certificate.general,k->Position(used,k));
    fi;
  od;
  record:=rec(schema_version:=1,action_id:=a.action_id,classes:=classrows,atoms:=atoms,characters:=chars,normals:=entries);
  if cmp<>fail then record.comparator:=cmp;fi;
  return record;
end;;

NBVerifyBase:=function(a,expected)
  local U,V,Z;
  NBRequire(a.degree=expected.degree and a.family=expected.family,"baseline action degree and family");
  if IsBound(expected.catalogue_locator) then
    NBRequire(a.catalogue_locator=expected.catalogue_locator,"baseline catalogue locator");
  else NBRequire(a.construction_index=expected.construction_index,"baseline construction index");fi;
  U:=NBGroup(a.generators);V:=NBGroup(expected.generators);
  NBRequire((U=V or IsConjugate(SymmetricGroup(a.degree),U,V)),"literal baseline action identity");
  NBRequire(Size(U)=a.order and a.order=expected.order and IsTransitive(U,[1..a.degree])
    and PrimeDivisors(Size(U))<>[2],"faithful nonbinary original action");
  Z:=Normalizer(SymmetricGroup(a.degree),U);
  NBRequire(Z=NBGroup(a.normalizer_generators) and Size(Z)=a.normalizer_order
    and a.normalizer_order=expected.normalizer_order,"original normalizer and weight");
  NBRequire(a.normal_count=expected.normal_count,"normal-list baseline count");
  return U;
end;;

NBVerifyAction:=function(a,expected,record)
  local U,ns,j,k,N,e,classes,positions,p,c,g,classsum,atoms,irr,ch,values,chi,
    chars,cert,K,l,t,hom,R,C,Q,phi,Z,cmp,E,heads,mixed,comparators;
  U:=NBVerifyBase(a,expected);
  NBRequire(record.schema_version=1 and record.action_id=a.action_id,"normal record identity");
  ns:=List(record.normals,e->NBGroup(e.generators));
  NBRequire(Length(ns)=a.normal_count,"all supplied normal records");
  for j in [1..Length(ns)] do
    N:=ns[j];NBRequire(IsSubgroup(U,N) and IsNormal(U,N) and Size(N)=record.normals[j].order,"literal normal subgroup/order");
    NBRequire(not ForAny([1..j-1],k->ns[k]=N),"distinct literal normal kernels");
  od;
  NBRequire(ForAny(ns,N->Size(N)=1) and U in ns,"trivial and whole normal kernels");
  classes:=ConjugacyClasses(U);positions:=[];classsum:=0;
  for c in record.classes do
    g:=PermList(c.representative);NBRequire(g in U,"literal conjugacy representative");
    p:=PositionProperty(classes,x->g in x);NBRequire(p<>fail and not p in positions,"distinct conjugacy classes");Add(positions,p);
    NBRequire(c.size=Size(U)/Size(Centralizer(U,g)),"class size from actual centralizer");classsum:=classsum+c.size;
    NBRequire(NormalClosure(U,Group(g))=ns[c.normal_closure],"literal class normal closure");
  od;
  NBRequire(classsum=Size(U),"complete conjugacy-class partition");
  NBRequire(Set(positions)=[1..Length(classes)],"character-table class correspondence");
  atoms:=Set(List(record.classes,c->c.normal_closure));NBRequire(atoms=record.atoms,"all class normal-closure atoms");
  for j in [1..Length(ns)] do
    NBRequire(Length(record.normals[j].joins)=Length(atoms),"complete normal-join row");
    for k in [1..Length(atoms)] do
      NBRequire(ClosureGroup(ns[j],ns[atoms[k]])=ns[record.normals[j].joins[k]],"closure under each class-normal join");
    od;
  od;
  irr:=Irr(U);NBRequire(ConjugacyClasses(CharacterTable(U))=classes,"computed character class order");chars:=[];
  for ch in record.characters do
    values:=List(ch.values,NBValue);
    chi:=First(irr,x->List(positions,k->x[k])=values);
    NBRequire(chi<>fail and DegreeOfCharacter(chi)=ch.degree,"actual irreducible with retained exact values");
    NBRequire(KernelOfCharacter(chi)=ns[ch.kernel],"literal character kernel");Add(chars,chi);
  od;
  cmp:=fail;
  if a.family="comparator" then
    E:=DerivedSubgroup(U);cmp:=record.comparator;
    NBRequire(ns[cmp.kernel]=E,"comparator kernel is original derived subgroup");
    R:=NBComparator();hom:=GroupHomomorphismByImages(U,R,GeneratorsOfGroup(U),List(cmp.generator_images,PermList));
    NBRequire(hom<>fail and IsGroupHomomorphism(hom) and Image(hom)=R and Kernel(hom)=E,"literal comparator onto-map and kernel");
  fi;
  heads:=0;mixed:=0;comparators:=0;
  for j in [1..Length(ns)] do
    N:=ns[j];cert:=record.normals[j].certificate;
    if a.family="comparator" and IsSubgroup(N,E) then NBRequire(cert.kind="comparator","entire derived quotient interval");fi;
    if cert.kind="mixed" then
      K:=U;for k in Concatenation(cert.linear,cert.general) do K:=Intersection(K,KernelOfCharacter(chars[k]));od;
      NBRequire(K=N,"one fixed tuple has exactly the original normal kernel");
      NBRequire(ForAll(cert.linear,k->DegreeOfCharacter(chars[k])=1),"designated linear characters");
      l:=Length(cert.linear);t:=Length(cert.general);
      NBRequire(3^(64*l)*5^(64*t)<=2^(24*a.degree-3),"exact mixed capacity reserve");mixed:=mixed+1;
    elif cert.kind="comparator" then
      NBRequire(a.family="comparator" and IsSubgroup(N,E),"comparator only on the complete retained interval");comparators:=comparators+1;
    elif cert.kind="head" then
      NBRequire(a.family="head","central-head family");C:=ns[cert.central_preimage];
      NBRequire(IsSubgroup(C,N),"central preimage contains original kernel");
      phi:=NaturalHomomorphismByNormalSubgroup(U,N);Q:=Image(phi);Z:=Image(phi,C);
      NBRequire(Z=Centre(Q) and IsElementaryAbelian(Z) and Size(Z)=2^cert.central_rank,"exact central elementary kernel");
      R:=NBModel(cert.model_type,cert.model_rank);
      hom:=GroupHomomorphismByImages(U,R,GeneratorsOfGroup(U),List(cert.generator_images,PermList));
      NBRequire(hom<>fail and IsGroupHomomorphism(hom) and Image(hom)=R and Kernel(hom)=C,"literal repeated-model quotient map");
      NBRequire(32*Maximum(cert.central_rank,cert.model_rank)<=127,"strict head capacity at original width");heads:=heads+1;
    else Error("NONBINARY: unknown certificate kind");fi;
  od;
  if a.family="mixed" then NBRequire(mixed=Length(ns),"mixed family complete");fi;
  Print("PASS NONBINARY ACTION ",a.action_id,": ",Length(ns)," normals; ",Length(record.classes)," classes; ",[mixed,comparators,heads]," certificates\n");
  return [Length(ns),mixed,comparators,heads];
end;;

NBVerifyCatalogue:=function()
  local i,U,a,count;
  NBRequire(LoadPackage("transgrp")<>fail,"TransGrp available");
  NBRequire(PackageInfo("transgrp")[1].Version=NonbinaryAlphabet.classification.transgrp_version,"pinned TransGrp release");
  NBRequire(NrTransitiveGroups(16)=1954,"published slice size");count:=0;
  for i in [1..1954] do
    U:=TransitiveGroup(16,i);a:=First(NonbinaryAlphabet.actions,a->a.catalogue_locator=[16,i]);
    if PrimeDivisors(Size(U))=[2] then NBRequire(a=fail,"binary class outside nonbinary package");
    else NBRequire(a<>fail and IsConjugate(SymmetricGroup(16),U,NBGroup(a.generators)),"literal action corresponds to indexed original class");count:=count+1;fi;
  od;
  NBRequire(count=527,"complete nonbinary catalogue slice");
  Print("PASS NONBINARY CATALOGUE: 527 nonbinary and 1427 binary classes in the pinned 1954-entry slice\n");
end;;
