# Literal coverage for the binary small-width certificate.
# Production may use TransGrp; verification does not query a group catalogue
# or NormalSubgroups. Coverage is checked from all index-two kernels and all
# central involution extensions, using the supplied literal action groups.

FCRequire := function(ok,msg)
  if not ok then Error(Concatenation("FINITE COVERAGE: ",msg)); fi;
end;;
FCPerms := function(gens,w) return List(gens,g->List([1..w],i->i^g)); end;;
FCGroup := function(rows)
  if Length(rows)=0 then return Group(()); fi;
  return Group(List(rows,PermList));
end;;
FCJSON:=fail;;FCWreath:=fail;;
FCHeader:=fail;;FCNodes:=fail;;FCSeen:=[];;FCReachEdges:=[];;FCCounters:=fail;;
FCPinnedBase:=[];;
FCJSON := function(v)
  local names;
  if IsBool(v) then return String(v); fi;
  if IsInt(v) then return String(v); fi;
  if IsStringRep(v) then
    return Concatenation("\"",ReplacedString(ReplacedString(ReplacedString(v,"\\","\\\\"),"\"","\\\""),"\n","\\n"),"\"");
  fi;
  if IsList(v) then return Concatenation("[",JoinStringsWithSeparator(List(v,FCJSON),","),"]"); fi;
  if IsRecord(v) then
    names:=SortedList(RecNames(v));
    return Concatenation("{",JoinStringsWithSeparator(List(names,k->Concatenation(FCJSON(k),":",FCJSON(v.(k)))),","),"}");
  fi;
  Error("non-JSON certificate value");
end;;
FCDataStream:=OutputTextUser();;SetPrintFormattingStatus(FCDataStream,false);;
FCEmit := function(v) PrintTo(FCDataStream,"DATA ",FCJSON(v),"\n"); end;;
FCId := function(w,i) return Concatenation("b",String(w),"_",String(i)); end;;

# Explicit Sylow-two action on 2^a points. A left copy and the half swap
# generate both copies at the next level. Its order is 2^(w-1).
FCWreath := function(w)
  local half,old,gens,g,row,i;
  if w=1 then return Group(()); fi;
  half:=w/2;old:=FCWreath(half);gens:=[];
  for g in GeneratorsOfGroup(old) do
    if g=() then continue; fi;
    row:=[1..w];for i in [1..half] do row[i]:=i^g;od;
    Add(gens,PermList(row));
  od;
  Add(gens,PermList(Concatenation([half+1..w],[1..half])));
  return Group(gens);
end;;

# Every nonzero functional on U/Phi(U) occurs once. The quotient generators
# are checked to be a basis, so no enumeration oracle supplies the child list.
FCIndexTwo := function(U)
  local phi,q,A,basis,d,C,out,mask,values,map,H;
  phi:=FrattiniSubgroup(U);q:=NaturalHomomorphismByNormalSubgroup(U,phi);
  A:=Image(q);basis:=SmallGeneratingSet(A);d:=Length(basis);
  FCRequire(IsElementaryAbelian(A) and Size(A)=2^d,"Frattini quotient basis");
  C:=Group((1,2));out:=[];
  for mask in [1..2^d-1] do
    values:=List([1..d],i->(1,2)^(QuoInt(mask,2^(i-1)) mod 2));
    map:=GroupHomomorphismByImages(A,C,basis,values);
    FCRequire(map<>fail and Size(Image(map))=2,"binary functional");
    H:=PreImage(q,Kernel(map));
    FCRequire(Size(U)=2*Size(H),"index-two child");
    Add(out,H);
  od;
  return out;
end;;

FCProduceActionEdges := function(U,w,nodes)
  local H,idx,target,c,edges;
  edges:=[];
  if Size(U)=w then return edges;fi;
  for H in FCIndexTwo(U) do
    if IsTransitive(H,[1..w]) then
      idx:=TransitiveIdentification(H);target:=LookupDictionary(nodes,FCId(w,idx));
      FCRequire(target<>fail,"transitive child missing from producer registry");
      c:=RepresentativeAction(SymmetricGroup(w),H,FCGroup(target.generators));
      FCRequire(c<>fail and H^c=FCGroup(target.generators),"producer conjugator");
      Add(edges,rec(generators:=FCPerms(SmallGeneratingSet(H),w),
        target:=target.id,conjugator:=List([1..w],i->i^c)));
    fi;
  od;
  return edges;
end;;

# Every normal subgroup is reachable from 1 by central-involution extensions:
# a nontrivial normal subgroup of a finite 2-group meets its centre.
FCNormalChildren := function(U,N,dict)
  local q,Q,z,H,j,out;
  q:=NaturalHomomorphismByNormalSubgroup(U,N);Q:=Image(q);out:=[];
  for z in Elements(Centre(Q)) do
    if Order(z)=2 then
      H:=ClosureGroup(N,PreImagesRepresentative(q,z));
      j:=LookupDictionary(dict,Set(Elements(H)));
      FCRequire(j<>fail,"central involution extension absent");Add(out,j);
    fi;
  od;
  return Set(out);
end;;

FCProduce := function(widths,degree16,degree8)
  local bases,nodes,registry,w,i,U,role,base,j,n,node,roots,W,c,header,
    normals,dict,context,entries,N,entry,edges,normalEdges,footer,counts,start,Z;
  start:=Runtime();bases:=FEWBuildBaseAlphabet();FEWSetBaseAlphabet(bases);
  FEWSetCharts(degree16,degree8);registry:=[];nodes:=NewDictionary("",true);
  for w in widths do
    for i in [1..NrTransitiveGroups(w)] do
      U:=TransitiveGroup(w,i);
      if not IsPGroup(U) or PrimeDivisors(Size(U))<>[2] then continue;fi;
      node:=rec(id:=FCId(w,i),degree:=w,generators:=FCPerms(GeneratorsOfGroup(U),w),
        order:=Size(U),catalogue_locator:=[w,i]);
      Z:=Normalizer(SymmetricGroup(w),U);
      node.normalizer_generators:=FCPerms(SmallGeneratingSet(Z),w);
      node.normalizer_order:=Size(Z);
      Add(registry,node);AddDictionary(nodes,node.id,node);
    od;
  od;
  roots:=[];
  for w in widths do
    W:=FCWreath(w);i:=TransitiveIdentification(W);node:=LookupDictionary(nodes,FCId(w,i));
    c:=RepresentativeAction(SymmetricGroup(w),W,FCGroup(node.generators));
    FCRequire(c<>fail and W^c=FCGroup(node.generators),"wreath root conjugator");
    Add(roots,rec(degree:=w,node:=node.id,conjugator:=List([1..w],i->i^c)));
  od;
  header:=rec(kind:="header",schema_version:=1,widths:=widths,nodes:=registry,
    roots:=roots,base_alphabet:=bases,degree16_chart:=degree16,degree8_charts:=degree8,
    producer:=rec(gap_version:=GAPInfo.Version,transgrp_version:=GAPInfo.PackagesInfo.transgrp[1].Version),
    coverage:="index_two_actions_and_central_involution_normals");
  FCEmit(header);
  counts:=rec(actions:=0,base_actions:=0,regular_actions:=0,nonregular_actions:=0,
    normals:=0,nonregular_normals:=0,action_edges:=0,normal_edges:=0,
    pair:=0,direct:=0,character:=0,transport:=0);
  for node in registry do
    w:=node.degree;U:=FEWGroup(node.generators,w);base:=FEWBaseMatch(U,w);
    edges:=FCProduceActionEdges(U,w,nodes);counts.action_edges:=counts.action_edges+Length(edges);
    if base<>fail then
      c:=RepresentativeAction(SymmetricGroup(w),U,FCGroup(bases[base].generators));
      n:=rec(kind:="action",id:=node.id,role:="base",base_index:=base,
        base_conjugator:=List([1..w],i->i^c),action_children:=edges,normals:=[]);
      counts.base_actions:=counts.base_actions+1;
    else
      if Size(U)=w then role:="regular";counts.regular_actions:=counts.regular_actions+1;
      else role:="nonregular";counts.nonregular_actions:=counts.nonregular_actions+1;fi;
      normals:=NormalSubgroups(U);dict:=NewDictionary([],true);
      for j in [1..Length(normals)] do AddDictionary(dict,Set(Elements(normals[j])),j);od;
      context:=FEWPrepare(U,w);entries:=[];
      for N in normals do
        entry:=FEWExport(context,N);
        FCRequire(entry<>fail,"normal entry has no witness");
        entry.children:=FCNormalChildren(U,N,dict);
        counts.normal_edges:=counts.normal_edges+Length(entry.children);
        counts.(entry.kind):=counts.(entry.kind)+1;
        Add(entries,entry);
      od;
      counts.normals:=counts.normals+Length(normals);
      if role="nonregular" then counts.nonregular_normals:=counts.nonregular_normals+Length(normals);fi;
      n:=rec(kind:="action",id:=node.id,role:=role,action_children:=edges,normals:=entries);
    fi;
    FCEmit(n);counts.actions:=counts.actions+1;
    if counts.actions mod 25=0 or w<16 then
      Print("PROGRESS exported ",counts.actions,"/",Length(registry)," actions; ",counts.normals," normals; ",Runtime()-start," ms\n");
    fi;
  od;
  footer:=rec(kind:="footer",schema_version:=1,counts:=counts);FCEmit(footer);
  Print("PASS FINITE MENU EXPORT: ",counts.actions," actions; ",counts.normals," literal normal witnesses\n");
end;;

FCVerifyBegin := function(header)
  local node,U,w,r,W,c,b,j,matched,Z;
  FCRequire(header.kind="header" and header.schema_version=1,"header schema");
  FCRequire(header.widths<>[] and Set(header.widths)=header.widths and
    ForAll(header.widths,w->w in [2,4,8,16]),"declared widths");
  FCHeader:=header;FCNodes:=NewDictionary("",true);FCSeen:=[];FCReachEdges:=[];
  FCCounters:=rec(actions:=0,base_actions:=0,regular_actions:=0,nonregular_actions:=0,
    normals:=0,nonregular_normals:=0,action_edges:=0,normal_edges:=0,
    pair:=0,direct:=0,character:=0,transport:=0);
  FCRequire(Length(FCPinnedBase)=17,"fixed release alphabet supplied");
  FEWCheckBaseAlphabet(header.base_alphabet);matched:=[];
  for b in header.base_alphabet do
    j:=PositionProperty(FCPinnedBase,x->x.degree=b.degree and x.role=b.role and
      IsConjugate(SymmetricGroup(b.degree),FEWGroup(b.generators,b.degree),FEWGroup(x.generators,x.degree)));
    FCRequire(j<>fail and not j in matched,"fixed literal base alphabet binding");Add(matched,j);
  od;
  FEWSetBaseAlphabet(header.base_alphabet);
  FEWSetCharts(header.degree16_chart,header.degree8_charts);
  for node in header.nodes do
    FCRequire(LookupDictionary(FCNodes,node.id)=fail,"duplicate action identifier");
    w:=node.degree;U:=FEWGroup(node.generators,w);
    FCRequire(w in header.widths and LargestMovedPoint(U)<=w and IsTransitive(U,[1..w]),"literal transitive action");
    FCRequire(Size(U)=node.order and IsPGroup(U) and PrimeDivisors(Size(U))=[2],"binary action order");
    Z:=FEWGroup(node.normalizer_generators,w);
    FCRequire(Size(Z)=node.normalizer_order and Z=Normalizer(SymmetricGroup(w),U),"exact original-action normalizer");
    AddDictionary(FCNodes,node.id,node);
  od;
  FCRequire(Set(List(header.roots,r->r.degree))=header.widths and Length(header.roots)=Length(header.widths),"one root per width");
  for r in header.roots do
    node:=LookupDictionary(FCNodes,r.node);FCRequire(node<>fail and node.degree=r.degree,"root target");
    W:=FCWreath(r.degree);c:=FEWPerms([r.conjugator],r.degree)[1];
    FCRequire(Size(W)=2^(r.degree-1) and W^c=FCGroup(node.generators),"explicit Sylow wreath root");
  od;
  Print("PROGRESS verified header: ",Length(header.nodes)," literal actions\n");
end;;

FCVerifyAction := function(record)
  local node,U,w,H,actual,edge,c,target,listed,keys,normalGroups,normalDict,j,N,
    e,children,base,b,normalEdges,reachable,changed,k,role;
  FCRequire(record.kind="action" and not record.id in FCSeen,"unique action record");
  node:=LookupDictionary(FCNodes,record.id);FCRequire(node<>fail,"registered action");
  w:=node.degree;U:=FEWGroup(node.generators,w);listed:=[];
  for edge in record.action_children do
    H:=FEWGroup(edge.generators,w);target:=LookupDictionary(FCNodes,edge.target);
    FCRequire(target<>fail and target.degree=w,"same-degree child target");
    c:=FEWPerms([edge.conjugator],w)[1];
    FCRequire(IsSubgroup(U,H) and Size(U)=2*Size(H) and IsTransitive(H,[1..w]),"literal transitive index-two child");
    FCRequire(H^c=FCGroup(target.generators),"literal child conjugator");
    Add(listed,Set(Elements(H)));Add(FCReachEdges,[record.id,edge.target]);
  od;
  if Size(U)=w then actual:=[];
  else actual:=List(Filtered(FCIndexTwo(U),H->IsTransitive(H,[1..w])),H->Set(Elements(H)));fi;
  FCRequire(Length(Set(listed))=Length(listed) and Set(listed)=Set(actual),"ALL transitive index-two children");
  FCCounters.action_edges:=FCCounters.action_edges+Length(listed);
  if record.role="base" then
    b:=record.base_index;FCRequire(b>=1 and b<=Length(FCHeader.base_alphabet),"base index");
    base:=FCHeader.base_alphabet[b];c:=FEWPerms([record.base_conjugator],w)[1];
    FCRequire(base.degree=w and U^c=FCGroup(base.generators),"literal base action binding");
    FCRequire(record.normals=[],"base exclusion scope");
    FCCounters.base_actions:=FCCounters.base_actions+1;
  else
    FCRequire(FEWBaseMatch(U,w)=fail,"nonbase action classification");
    if Size(U)=w then role:="regular";FCCounters.regular_actions:=FCCounters.regular_actions+1;
    else role:="nonregular";FCCounters.nonregular_actions:=FCCounters.nonregular_actions+1;fi;
    FCRequire(record.role=role,"regular/nonregular scope");
    normalGroups:=[];normalDict:=NewDictionary([],true);
    for j in [1..Length(record.normals)] do
      e:=record.normals[j];N:=FEWGroup(e.normal_generators,w);
      FCRequire(IsSubgroup(U,N) and IsNormal(U,N) and Size(N)=e.normal_order,"literal normal subgroup");
      FCRequire(LookupDictionary(normalDict,Set(Elements(N)))=fail,"distinct literal normal subgroups");
      Add(normalGroups,N);AddDictionary(normalDict,Set(Elements(N)),j);
    od;
    FCRequire(LookupDictionary(normalDict,[()])<>fail,"normal coverage starts at identity");
    for j in [1..Length(normalGroups)] do
      N:=normalGroups[j];e:=record.normals[j];
      FEWCheck(U,N,e);
      children:=FCNormalChildren(U,N,normalDict);
      FCRequire(e.children=Set(e.children) and e.children=children,"ALL central involution extensions");
      for k in children do FCRequire(Size(normalGroups[k])=2*Size(N),"strict normal-DAG growth");od;
      FCCounters.normal_edges:=FCCounters.normal_edges+Length(children);
      FCCounters.(e.kind):=FCCounters.(e.kind)+1;
    od;
    FCCounters.normals:=FCCounters.normals+Length(normalGroups);
    if role="nonregular" then FCCounters.nonregular_normals:=FCCounters.nonregular_normals+Length(normalGroups);fi;
  fi;
  Add(FCSeen,record.id);FCCounters.actions:=FCCounters.actions+1;
  if FCCounters.actions mod 25=0 or w<16 then
    Print("PROGRESS checked ",FCCounters.actions,"/",Length(FCHeader.nodes)," actions; ",FCCounters.normals," normals\n");
  fi;
end;;

FCVerifyEnd := function(footer)
  local reached,edge,changed;
  FCRequire(footer.kind="footer" and footer.schema_version=1,"footer schema");
  FCRequire(Set(FCSeen)=Set(List(FCHeader.nodes,n->n.id)),"every registered node processed");
  reached:=Set(List(FCHeader.roots,r->r.node));changed:=true;
  while changed do
    changed:=false;
    for edge in FCReachEdges do
      if edge[1] in reached and not edge[2] in reached then AddSet(reached,edge[2]);changed:=true;fi;
    od;
  od;
  FCRequire(reached=Set(FCSeen),"all nodes reachable from Sylow roots");
  FCRequire(FCCounters=footer.counts,"recomputed aggregate counts");
  Print("PASS FINITE MENU VERIFY: ",FCCounters.actions," actions; ",FCCounters.normals,
    " literal normal witnesses; ",FCCounters.action_edges," action edges; ",FCCounters.normal_edges," normal edges\n");
end;;
