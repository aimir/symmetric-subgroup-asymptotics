#!/usr/bin/env python3
"""Export or replay the constructive six-pair action and all-normal certificate."""
import argparse,gzip,json,os,sys,tempfile
from pathlib import Path
sys.dont_write_bytecode=True
from finite_menu import gap_literal,gap_command,prologue,run_gap,require
ROOT=Path(__file__).resolve().parents[2]
DATA=ROOT/'certificates/data/six_block.json.gz'
def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--gap-command')
    parser.add_argument('--timeout',type=int,default=7200)
    sub=parser.add_subparsers(dest='mode',required=True)
    p=sub.add_parser('export');p.add_argument('--output',type=Path,default=DATA);p.add_argument('--force',action='store_true')
    p=sub.add_parser('verify');p.add_argument('--input',type=Path,default=DATA)
    args=parser.parse_args();require(args.timeout>0,'positive timeout required')
    values=[]
    with tempfile.TemporaryDirectory(prefix='six-block-') as tmp:
        driver=Path(tmp)/'driver.g'
        code=prologue()+'Read('+gap_literal(str(ROOT/'computations/gap/six_block.g'))+');;\n'
        if args.mode=='export':
            require(args.force or not args.output.exists(),'output exists; use --force')
            code+='SBProduce();;\nQUIT;\n'
        else:
            with gzip.open(args.input,'rt') as f:data=json.load(f)
            code+='SBVerify('+gap_literal(data)+');;\nQUIT;\n'
        driver.write_text(code)
        passed=run_gap(gap_command(args.gap_command),driver,args.timeout,values.append if args.mode=='export' else None)
        require(any(p.startswith('PASS SIX BLOCK '+args.mode.upper()+':') for p in passed),'missing complete verdict')
    if args.mode=='export':
        require(len(values)==1,'exactly one complete data object required')
        args.output.parent.mkdir(parents=True,exist_ok=True)
        temporary=args.output.with_name(args.output.name+'.partial')
        try:
            with temporary.open('wb') as raw:
                with gzip.GzipFile(filename='',fileobj=raw,mode='wb',mtime=0) as f:
                    f.write((json.dumps(values[0],sort_keys=True,separators=(',',':'))+'\n').encode())
            os.replace(temporary,args.output)
        finally:
            if temporary.exists():temporary.unlink()
        print('WROTE',args.output)
    return 0
if __name__=='__main__':
    try:sys.exit(main())
    except (OSError,EOFError,ValueError) as error:
        print('FAIL:',error,file=sys.stderr);sys.exit(1)
