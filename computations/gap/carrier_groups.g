# Carrier normal-profile certificate and literal master maps.
# Producer: NormalSubgroups is allowed. Checker: no catalogue or normal-
# subgroup enumeration query; supplied lists are closed under every central
# involution extension and reachable from 1.

CCChecks:=0;;
CCRequire:=function(ok,label)
  CCChecks:=CCChecks+1;
  if not ok then Error(Concatenation("CARRIER: ",label));fi;
end;;
CCGroup:=function(rows)
  if Length(rows)=0 then return Group(());fi;
  return Group(List(rows,PermList));
end;;
CCPerms:=function(gens,w) return List(gens,g->List([1..w],i->i^g));end;;
CCId:=function(a) return Concatenation(String(a.degree),"T",String(a.catalogue_locator[2]));end;;
CCAction:=function(id)
  local a;
  a:=First(CarrierAlphabet.actions,a->CCId(a)=id);
  CCRequire(a<>fail,"missing literal action");return a;
end;;
CCLog:=function(n)
  local k;
  k:=LogInt(n,2);CCRequire(n=2^k,"positive power of two");return k;
end;;
CCRelative:=function(U,N)
  local D,R,k;
  D:=CommutatorSubgroup(N,U);
  R:=Group(Concatenation([()],GeneratorsOfGroup(D),List(GeneratorsOfGroup(N),x->x^2)));
  CCRequire(IsNormal(U,R) and IsSubgroup(N,R),"relative radical");
  k:=CCLog(Size(N)/Size(R));
  CCRequire(IsElementaryAbelian(N/R),"relative quotient elementary");
  return rec(rank:=k,radical:=R);
end;;
CCContext:=function(U,normals)
  local pairs,ranks,levels,buckets;
  pairs:=List(normals,N->CCRelative(U,N));ranks:=List(pairs,x->x.rank);
  levels:=Reversed(Set(ranks));
  buckets:=List(levels,r->Filtered([1..Length(normals)],i->ranks[i]=r));
  return rec(derived:=DerivedSubgroup(U),pairs:=pairs,levels:=levels,buckets:=buckets);
end;;
CCRow:=function(U,N,j,normals,context)
  local cap,level,m,a2,Q,c,g;
  cap:=Intersection(N,context.derived);m:=fail;
  for level in [1..Length(context.levels)] do
    if ForAny(context.buckets[level],i->IsSubgroup(cap,normals[i])) then
      m:=context.levels[level];break;
    fi;
  od;
  CCRequire(m<>fail,"maximum relative derived-normal rank exists");
  a2:=CCRelative(U,context.pairs[j].radical).rank;Q:=U/N;
  if IsAbelian(Q) then c:=CCLog(Size(Q));g:=0;
  else c:=CCLog(Size(Centre(Q)));g:=CCLog(Size(DerivedSubgroup(Q)));fi;
  return [context.pairs[j].rank,CCLog(Size(N)),m,a2,c,g];
end;;

# This is the same finite closure criterion used by the binary menu checker.
# If 1<M normal U/N, then M meets Z(U/N) nontrivially; it contains an
# involution there. Hence every normal subgroup is reached inductively.
CCChildren:=function(U,N,dict)
  local q,Q,z,M,j,out;
  q:=NaturalHomomorphismByNormalSubgroup(U,N);Q:=Image(q);out:=[];
  for z in Elements(Centre(Q)) do
    if Order(z)=2 then
      M:=ClosureGroup(N,PreImagesRepresentative(q,z));
      j:=LookupDictionary(dict,Set(Elements(M)));
      CCRequire(j<>fail,"missing central-involution extension");Add(out,j);
    fi;
  od;
  return Set(out);
end;;

CCJSON:=fail;;
CCJSON:=function(v)
  local keys;
  if IsInt(v) then return String(v);fi;
  if IsStringRep(v) then return Concatenation("\"",v,"\"");fi;
  if IsList(v) then return Concatenation("[",JoinStringsWithSeparator(List(v,CCJSON),","),"]");fi;
  if IsRecord(v) then
    keys:=SortedList(RecNames(v));
    return Concatenation("{",JoinStringsWithSeparator(List(keys,k->Concatenation(CCJSON(k),":",CCJSON(v.(k)))),","),"}");
  fi;
  Error("unsupported carrier producer value");
end;;

CCVerifyBase:=function()
  local a,expected,U,V,c;
  CCRequire(Set(List(CarrierAlphabet.actions,CCId))=Set(List(CarrierExpectedAlphabet.actions,CCId))
    and Length(CarrierAlphabet.actions)=Length(CarrierExpectedAlphabet.actions),"exact baseline action IDs");
  for a in CarrierAlphabet.actions do
    expected:=First(CarrierExpectedAlphabet.actions,b->CCId(b)=CCId(a));
    CCRequire(a.degree=expected.degree and a.role=expected.role,"baseline action degree and role");
    U:=CCGroup(a.generators);V:=CCGroup(expected.generators);
    c:=RepresentativeAction(SymmetricGroup(a.degree),U,V);
    CCRequire(c<>fail and U^c=V,"permutation conjugacy to the committed baseline action");
    CCRequire(a.order=expected.order and a.normalizer_order=expected.normalizer_order,"baseline action weights");
  od;
  Print("PASS CARRIER BASE: literal permutation conjugacy to the committed alphabet\n");
end;;

CCProduce:=function()
  local item,a,U,normals,dict,j,context,entries,row,output;
  output:=OutputTextUser();SetPrintFormattingStatus(output,false);
  for item in CarrierTransitions.masters do
    a:=CCAction(item.action_id);U:=CCGroup(a.generators);
    normals:=NormalSubgroups(U);dict:=NewDictionary([],true);
    for j in [1..Length(normals)] do AddDictionary(dict,Set(Elements(normals[j])),j);od;
    context:=CCContext(U,normals);entries:=[];
    for j in [1..Length(normals)] do
      row:=CCRow(U,normals[j],j,normals,context);
      Add(entries,rec(normal_generators:=CCPerms(SmallGeneratingSet(normals[j]),a.degree),
        order:=Size(normals[j]),row:=row,children:=CCChildren(U,normals[j],dict)));
    od;
    PrintTo(output,"DATA ",CCJSON(rec(schema_version:=1,action_id:=item.action_id,
      normals:=entries)),"\n");
    Print("PRODUCED CARRIER ",item.action_id," ",Length(entries),"\n");
  od;
  Print("PASS CARRIER PRODUCTION\n");
end;;

CCVerifyNormals:=function(record)
  local item,a,U,normals,dict,j,N,entry,context,rows,children,seen,todo,k,
    expected,actual,edges,empty;
  CCRequire(record.schema_version=1,"normal data schema");
  item:=First(CarrierTransitions.masters,x->x.action_id=record.action_id);
  CCRequire(item<>fail,"unexpected normal-profile action");
  a:=CCAction(item.action_id);U:=CCGroup(a.generators);
  CCRequire(a.role="carrier" and Size(U)=a.order and IsTransitive(U,[1..a.degree]),
    "original carrier action for the normal profile");
  CCLog(Size(U));
  normals:=List(record.normals,e->CCGroup(e.normal_generators));dict:=NewDictionary([],true);
  empty:=fail;edges:=0;
  for j in [1..Length(normals)] do
    N:=normals[j];entry:=record.normals[j];
    CCRequire(IsSubgroup(U,N) and IsNormal(U,N),"literal normal subgroup");
    CCRequire(Size(N)=entry.order,"literal normal order");
    CCRequire(LookupDictionary(dict,Set(Elements(N)))=fail,"duplicate literal kernel");
    AddDictionary(dict,Set(Elements(N)),j);
    if Size(N)=1 then empty:=j;fi;
  od;
  CCRequire(empty<>fail,"trivial kernel present");
  for j in [1..Length(normals)] do
    children:=CCChildren(U,normals[j],dict);
    CCRequire(record.normals[j].children=children,"complete child list");
    for k in children do CCRequire(Size(normals[k])=2*Size(normals[j]),"strict binary edge");od;
    edges:=edges+Length(children);
  od;
  seen:=[empty];todo:=[empty];
  while Length(todo)>0 do
    j:=Remove(todo);
    for k in record.normals[j].children do
      if not k in seen then Add(seen,k);Add(todo,k);fi;
    od;
  od;
  CCRequire(Length(seen)=Length(normals),"every supplied kernel reached from 1");
  context:=CCContext(U,normals);rows:=[];
  for j in [1..Length(normals)] do
    entry:=record.normals[j];actual:=CCRow(U,normals[j],j,normals,context);
    CCRequire(actual=entry.row,"exact six-parameter literal row");
    if a.degree=16 then
      CCRequire(actual[4]<=actual[3],"safe a2 inflation");
      Add(rows,actual{[1,2,3,5,6]});
    else Add(rows,actual);fi;
  od;
  if a.degree=16 then
    CCRequire(FrattiniSubgroup(U)=DerivedSubgroup(U),"degree-sixteen radical hypothesis");
  fi;
  expected:=List(item.profile,e->[e.row,e.multiplicity]);
  CCRequire(Collected(rows)=SortedList(expected),"complete profile equals numerical data");
  Print("PASS CARRIER NORMALS ",record.action_id,": ",Length(normals)," kernels; ",edges," edges\n");
  return [Length(normals),edges];
end;;

CCVerifyMaps:=function()
  local a,U,normalizer,r,source,target,S,T,gens,images,map,K,targets,
    C,D,E,sg,tg,pi,chi,nat,iso,N,character,targetGens,targetImages,psi,H,pre,i;
  for a in CarrierAlphabet.actions do
    if not a.role="carrier" then continue;fi;
    U:=CCGroup(a.generators);
    CCRequire(IsTransitive(U,[1..a.degree]),"original carrier action transitive");
    CCRequire(Size(U)=a.order,"original action order");
    normalizer:=Normalizer(SymmetricGroup(a.degree),U);
    CCRequire(Size(normalizer)=a.normalizer_order,"complete original action normalizer");
  od;
  CCRequire(CarrierMaps.schema_version=1 and CarrierMaps.degree=8,"map schema");
  CCRequire(List(CarrierMaps.routes,r->[r.source,r.target])=
    [["8T26","8T26"],["8T27","8T27"],["8T27","8T28"],
     ["8T35","8T18"],["8T35","8T29"],["8T35","8T31"],["8T35","8T35"]],
    "exact master-to-original route pairs");
  targets:=[];
  for r in CarrierMaps.routes do
    source:=CCAction(r.source);target:=CCAction(r.target);
    CCRequire(source.degree=8 and target.degree=8,"unchanged physical map degree");
    S:=CCGroup(source.generators);T:=CCGroup(target.generators);
    gens:=List(source.generators,PermList);images:=List(r.source_generator_images,PermList);
    CCRequire(Length(gens)=Length(images),"image alignment");
    map:=GroupHomomorphismByImages(S,T,gens,images);
    CCRequire(map<>fail and IsGroupHomomorphism(map),"literal master map is a homomorphism");
    CCRequire(Image(map)=T,"literal master map is onto");
    K:=CCGroup(r.kernel_generators);
    CCRequire(Kernel(map)=K and Size(K)=r.kernel_order,"literal master kernel");
    Add(targets,r.target);
    # A proper graph over a retained external C2 is a correlated full source.
    # Its full preimage tests recovery and both displayed projections.
    C:=Group((1,2));D:=DirectProduct(C,S);E:=DirectProduct(C,T);
    sg:=Concatenation(List(GeneratorsOfGroup(C),g->Image(Embedding(D,1),g)),
       List(gens,g->Image(Embedding(D,2),g)));
    tg:=Concatenation(List(GeneratorsOfGroup(C),g->Image(Embedding(E,1),g)),
       List(images,g->Image(Embedding(E,2),g)));
    pi:=GroupHomomorphismByImages(D,E,sg,tg);
    CCRequire(pi<>fail and Image(pi)=E,"product master map");
    N:=FrattiniSubgroup(T);nat:=NaturalHomomorphismByNormalSubgroup(T,N);
    U:=Image(nat);targetGens:=SmallGeneratingSet(U);
    CCRequire(IsElementaryAbelian(U) and Size(U)=2^Length(targetGens),"character basis");
    targetImages:=List([1..Length(targetGens)],function(i) if i=1 then return (1,2);else return ();fi;end);
    chi:=GroupHomomorphismByImages(U,C,targetGens,targetImages);
    sg:=Concatenation(List(GeneratorsOfGroup(C),g->Image(Embedding(E,1),g)),
       List(GeneratorsOfGroup(T),g->Image(Embedding(E,2),g)));
    tg:=Concatenation(GeneratorsOfGroup(C),List(GeneratorsOfGroup(T),g->Image(chi,Image(nat,g))));
    psi:=GroupHomomorphismByImages(E,C,sg,tg);H:=Kernel(psi);pre:=PreImage(pi,H);
    CCRequire(Size(H)*2=Size(E) and Image(pi,pre)=H,"correlated inverse recovery");
    CCRequire(Image(Projection(E,1),H)=C and Image(Projection(E,2),H)=T,"target fullness");
    CCRequire(Image(Projection(D,1),pre)=C and Image(Projection(D,2),pre)=S,"master fullness");
  od;
  CCRequire(Set(targets)=["8T18","8T26","8T27","8T28","8T29","8T31","8T35"]
    and Length(targets)=7,"all original degree-eight colours routed exactly once");
  Print("PASS CARRIER MAPS: 7 generator-image maps and correlated full preimages\n");
end;;
