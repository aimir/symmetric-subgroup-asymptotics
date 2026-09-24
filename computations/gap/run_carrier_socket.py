#!/usr/bin/env python3
"""Verify all twelve carrier Bockstein profiles and correlated pullback controls."""
import argparse,json,sys,tempfile
from pathlib import Path
sys.dont_write_bytecode=True
from finite_menu import gap_literal,gap_command,prologue,run_gap,require
ROOT=Path(__file__).resolve().parents[2]
def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--data',type=Path,default=ROOT/'certificates/data/carrier_socket.json')
    parser.add_argument('--gap-command')
    parser.add_argument('--timeout',type=int,default=600)
    args=parser.parse_args()
    require(args.timeout>0,'positive timeout required')
    data=json.loads(args.data.read_text())
    alphabet=json.loads((ROOT/'certificates/data/base_alphabet.json').read_text())
    with tempfile.TemporaryDirectory(prefix='carrier-socket-') as tmp:
        driver=Path(tmp)/'driver.g'
        driver.write_text(prologue()+'SocketData:='+gap_literal(data)+';;\nSocketAlphabet:='+gap_literal(alphabet)+';;\nRead('+gap_literal(str(ROOT/'computations/gap/carrier_socket.g'))+');;\nQUIT;\n')
        passed=run_gap(gap_command(args.gap_command),driver,args.timeout)
        require(any(p.startswith('PASS CARRIER SOCKET:') for p in passed),'missing socket verdict')
    return 0
if __name__=='__main__':
    try:sys.exit(main())
    except (ValueError,OSError,EOFError) as error:
        print('FAIL:',error,file=sys.stderr);sys.exit(1)
