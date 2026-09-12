#!/usr/bin/env python3
import os
import glob
import subprocess
from concurrent.futures import ProcessPoolExecutor, as_completed

import sys

SCRIPTS = [
    "dump-ir",
    "dump-lcnf-saveBase",
    "dump-lcnf-saveMono",
    "dump-lcnf-saveResult",
    "dump-array-own",
    "dump-hash-repr",
    "dump-io-abi",
    "dump-option-repr",
    "dump-param-plan",
    "dump-split-plan"
]

def all_txt_exist(dir_path, stem):
    return all(
        os.path.exists(os.path.join(dir_path, f"{stem}-{s}.txt"))
        for s in SCRIPTS
    )

def run_one(args):
    dir_path, stem, force = args
    cmd = ["lake", "env", "lean", "--run", "scripts/generate-all-dumps.lean"]
    if force:
        cmd.append("--force")
    cmd.extend([dir_path, stem])
    res = subprocess.run(cmd, capture_output=True, text=True)
    out = (res.stdout + "\n" + res.stderr).strip()
    return dir_path, stem, res.returncode, out

def main():
    force = "--force" in sys.argv
    dirs = ["LeanJsCliSnapshots", "LeanJsCliSnapshots2"]
    pending = []
    already_done = 0

    for d in dirs:
        lean_files = sorted(glob.glob(os.path.join(d, "*.lean")))
        for f in lean_files:
            stem = os.path.basename(f)[:-5]
            if not force and all_txt_exist(d, stem):
                already_done += 1
            else:
                pending.append((d, stem, force))

    if force:
        print("Running in --force mode (regenerating all files)")
    print(f"Already completed: {already_done}")
    print(f"Pending to process: {len(pending)}")

    failed = []
    success = 0

    # Run with 4 parallel worker processes
    with ProcessPoolExecutor(max_workers=4) as executor:
        futures = {executor.submit(run_one, item): item for item in pending}
        for future in as_completed(futures):
            d, stem, rc, out = future.result()
            if rc == 0 and "✗" not in out:
                success += 1
                print(f"  [OK] {d}/{stem}")
            else:
                failed.append((d, stem, out))
                print(f"  [ERROR] {d}/{stem}: {out[:100]}...")

    print("\n" + "="*50)
    print("SUMMARY")
    print("="*50)
    print(f"Total already done previously: {already_done}")
    print(f"Successfully processed now: {success}")
    print(f"Failed to generate: {len(failed)}")

    if failed:
        print("\nFiles that could not be generated due to mistakes in Lean source:")
        for d, stem, out in failed:
            print(f"- {d}/{stem}.lean")
            first_err = [line for line in out.splitlines() if "❌" in line or "error:" in line or "✗" in line]
            if first_err:
                print(f"  Reason: {first_err[0]}")
            else:
                print(f"  Reason: {out[:150]}")

if __name__ == "__main__":
    main()
