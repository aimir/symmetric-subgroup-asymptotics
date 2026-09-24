"""Independent exhaustive F2^16 cyclic-submodule closure, no MeatAxe/catalogue."""
import json
from pathlib import Path

def require(condition, message):
    if not condition:
        raise ValueError(message)

def basis(vs):
    rows=[0]*16
    for v in vs:
        while v:
            p=v.bit_length()-1
            if rows[p]: v ^= rows[p]
            else:
                rows[p]=v
                break
    for p in range(16):
        if rows[p]:
            for q in range(p+1,16):
                if rows[q]>>p&1: rows[q]^=rows[p]
    return tuple(v for v in rows if v)

def contains(B,v):
    for row in reversed(B):
        if v>>(row.bit_length()-1)&1: v^=row
    return v==0

records=json.loads(Path(__file__).with_name('frames8.json').read_text())
frame_count=0
sum_checks=0
module_checks=0
orbit_count=0
for rec in records:
    idx,order,local,kernel,z,ceiling,mu,mats,raw=rec
    modules={basis(B) for B in raw}
    require(len(modules)==len(raw), 'module certificate check at source line 37')
    require(() in modules and basis(1<<i for i in range(16)) in modules, 'module certificate check at source line 38')
    tables=[]
    for mat in mats:
        require(len(mat)==16 and len(basis(mat))==16, 'module certificate check at source line 41')
        table=[0]*65536
        for v in range(1,65536):
            low=v&-v
            table[v]=table[v-low]^mat[low.bit_length()-1]
        tables.append(table)
    # Every vector lies in an explicitly enumerated orbit. Its orbit span
    # is its cyclic submodule. This exhausts cyclic modules independently.
    seen=bytearray(65536)
    cyc=set()
    local_orbits=0
    for v in range(65536):
        if seen[v]: continue
        orbit=[v]
        seen[v]=1
        for u in orbit:
            for table in tables:
                w=table[u]
                if not seen[w]: seen[w]=1;orbit.append(w)
        cyc.add(basis(orbit))
        local_orbits+=1
    require(all(seen), 'module certificate check at source line 62')
    require(cyc <= modules, 'module certificate check at source line 63')
    local_checks=0
    values=[]
    for B in modules:
        require(all(contains(B,table[v]) for table in tables for v in B), 'module certificate check at source line 67')
        comm=basis(table[v]^v for table in tables for v in B)
        values.append(len(B)-len(comm))
        for C in cyc:
            require(basis(B+C) in modules, 'module certificate check at source line 71')
            local_checks+=1
    # Starting at zero and adjoining a vector's cyclic module reaches every
    # invariant submodule; the checked sum closure proves completeness.
    require(max(values)==mu and mu<=2 and z<=2 and mu+z<=4, 'module certificate check at source line 75')
    frame_count+=1
    module_checks+=len(modules)
    orbit_count+=local_orbits
    sum_checks+=local_checks
    print('EXACT MODULE CLOSURE',[idx,order,local,kernel,len(modules),len(cyc),local_orbits,local_checks,mu],flush=True)
require(frame_count==30 and module_checks==812, 'module certificate check at source line 81')
require(orbit_count==21892 and sum_checks==39449, 'module certificate check at source line 82')
print('FINAL INDEPENDENT EIGHT-FRAME MODULE CLOSURE: PASS',frame_count,'frames;',module_checks,'invariant modules;',orbit_count,'complete vector orbits;',sum_checks,'cyclic-sum closure cells; all heads<=2')
