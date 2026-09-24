#!/usr/bin/env python3
"""Focused frame checks; no historical-tree dependency or broad census."""
import argparse
import json
from pathlib import Path
import re
import shlex
import shutil
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parent


def gap_check(part, command, timeout):
    code = ('SizeScreen([1000000,1000000]);;\n'
            'FrameEightTops:=[];;FrameEightBindings:=[];;FrameEightModules:=[];;\n'
            'AffineFourDZeroClasses:=[];;DZeroUnpairedSixteenCertificates:=[];;\n'
            'DZeroPrimitiveEightLocalRows:=[];;\n')
    if part == 'groups8':
        data = json.loads((ROOT / 'frames8.json').read_text())
        code += 'FrameEightModules:=' + json.dumps(data, separators=(',', ':')) + ';;\n'
        code += 'Read("bindings8.g");;\n'
    else:
        code += 'Read("tops16.g");;\nRead("frames16.g");;\n'
    code += 'Read("verify_frames.g");;\n'
    code += ('VerifyFramesEight();;\n' if part == 'groups8' else 'VerifyFramesSixteen();;\n')
    code += 'Print("PASS FRAME CHECK COMPLETE\\n");;\nQUIT;\n'
    with tempfile.NamedTemporaryFile('w', suffix='.g') as driver:
        driver.write(code)
        driver.flush()
        result = subprocess.run(command + ['-q', '-T', driver.name], cwd=ROOT,
                                text=True, capture_output=True, timeout=timeout)
    output = result.stdout + result.stderr
    print(output, end='')
    if (result.returncode or re.search(r'\bError\b|Syntax warning|FAIL', output)
            or 'PASS FRAME CHECK COMPLETE' not in output):
        raise SystemExit('Frame verification did not complete successfully.')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--part', choices=['all', 'modules8', 'groups8', 'groups16'], default='all')
    parser.add_argument('--gap-command', help="GAP invocation, for example '/path/to/sage --gap'")
    parser.add_argument('--timeout', type=int, default=600)
    args = parser.parse_args()
    if args.part in ('all', 'modules8'):
        import sys
        subprocess.run([sys.executable, str(ROOT / 'verify_modules8.py')], check=True,
                       cwd=ROOT, timeout=args.timeout)
    if args.part == 'modules8':
        return
    if args.gap_command:
        command = shlex.split(args.gap_command)
    elif shutil.which('gap'):
        command = [shutil.which('gap')]
    elif shutil.which('sage'):
        command = [shutil.which('sage'), '--gap']
    else:
        raise SystemExit('GAP is required; pass --gap-command.')
    for part in (['groups8', 'groups16'] if args.part == 'all' else [args.part]):
        gap_check(part, command, args.timeout)


if __name__ == '__main__':
    main()
