#!/usr/bin/env python3
"""Check that an omitted module and a false fixed-space witness are rejected."""
import argparse
import json
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parent


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--gap-command', default='sage --gap')
    args = parser.parse_args()
    with tempfile.TemporaryDirectory() as temp:
        target = Path(temp)
        for name in ['frames8.json', 'verify_modules8.py', 'frames16.g',
                     'tops16.g', 'verify_frames.g', 'run_frames.py']:
            shutil.copy2(ROOT / name, target / name)
        data = json.loads((target / 'frames8.json').read_text())
        data[0][8].pop()
        (target / 'frames8.json').write_text(json.dumps(data))
        result = subprocess.run([sys.executable, str(target / 'verify_modules8.py')],
                                text=True, capture_output=True, timeout=120)
        if result.returncode == 0 or 'ValueError' not in result.stderr:
            raise SystemExit('Omitted invariant module was not rejected.')
        data = (target / 'frames16.g').read_text()
        pattern = r'(\[\s*1,\s*48,\s*0,\s*3,\s*1,\s*3,\s*1,\s*)10(,\s*)10(\s*\])'
        data, count = re.subn(pattern, r'\g<1>11\g<2>11\g<3>', data, count=1)
        if count != 1:
            raise SystemExit('Expected first frame witness was not found.')
        (target / 'frames16.g').write_text(data)
        result = subprocess.run([sys.executable, str(target / 'run_frames.py'),
                                 '--part', 'groups16', '--gap-command', args.gap_command],
                                text=True, capture_output=True, timeout=120)
        if (result.returncode == 0
                or 'constructed-top numerical row' not in result.stdout):
            raise SystemExit('False fixed-space dimension was not rejected.')
    print('PASS NEGATIVE FRAME CONTROLS: omitted module and false fixed-space dimension rejected')


if __name__ == '__main__':
    main()
