# Optional DATA PRODUCER, not a verification or completeness proof.
# Requires GAP's transitive-group catalogue. Writes JSON to stdout.
# Run: gap -q -T computations/gap/export_degree8_charts.g > candidate.json
SizeScreen([1000000,1000000]);;
ExportDegree8Charts:=function()
 local array,V,vg,i,U,ug,N,a0,Q0,regular,Q,a,b0,b,first;
 array:=function(gs,d) return List(gs,g->List([1..d],x->x^g));end;
 V:=TransitiveGroup(8,27);vg:=GeneratorsOfGroup(V);
 Print("{\n  \"schema_version\": 1,\n  \"degree\": 8,\n  \"cover_library_locator\": \"8T27\",\n  \"cover_generators\": ",array(vg,8),",\n  \"charts\": [\n");
 first:=true;
 for i in [16,20,21] do
   U:=TransitiveGroup(8,i);ug:=GeneratorsOfGroup(U);
   N:=First(NormalSubgroups(U),x->Size(x)=2);
   if N=fail then Error("missing source normal axis");fi;
   a0:=NaturalHomomorphismByNormalSubgroup(U,N);Q0:=Image(a0);
   regular:=ActionHomomorphism(Q0,Elements(Q0),OnRight);Q:=Image(regular);
   a:=CompositionMapping(regular,a0);b0:=First(GQuotients(V,Q0));
   if b0=fail then Error("missing carrier quotient map");fi;
   b:=CompositionMapping(regular,b0);
   if not first then Print(",\n");fi;first:=false;
   Print("    {\n      \"source_library_locator\": \"8T",i,"\",\n",
     "      \"source_generators\": ",array(ug,8),",\n",
     "      \"kernel_generators\": ",array(GeneratorsOfGroup(N),8),",\n",
     "      \"quotient_degree\": 16,\n",
     "      \"quotient_generators\": ",array(GeneratorsOfGroup(Q),16),",\n",
     "      \"alpha_images\": ",array(List(ug,g->Image(a,g)),16),",\n",
     "      \"beta_images\": ",array(List(vg,g->Image(b,g)),16),",\n",
     "      \"cover_kernel_generators\": ",array(GeneratorsOfGroup(Kernel(b)),8),",\n",
     "      \"source_order\": 32, \"kernel_order\": 2, \"cover_order\": 64, \"quotient_order\": 16\n    }");
 od;
 Print("\n  ]\n}\n");
end;;
ExportDegree8Charts();
QUIT_GAP(0);
