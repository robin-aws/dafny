import argparse
import subprocess
import sys
import os
import pathlib

def run_subprocess(cmd: str, *args: str, check = True, **kwargs) -> subprocess.CompletedProcess:
    print([cmd, *args])

    result = subprocess.run([cmd, *args], # pylint: disable=subprocess-run-check
        **{"capture_output": True, "check": False, "encoding": "utf-8", **kwargs})
    if check:
      result.check_returncode()
    result

def git(cmd: str, *args: str, **kwargs) -> subprocess.CompletedProcess:
    return run_subprocess("git", *[cmd, *args], **kwargs)

def dotnet(cmd: str, *args: str, **kwargs) -> subprocess.CompletedProcess:
    return run_subprocess("dotnet", *[cmd, *args], **kwargs)

def dafny(cmd: str, *args: str, **kwargs) -> subprocess.CompletedProcess:
    return run_subprocess("Scripts/dafny", *[cmd, *args], **kwargs)

def make(cmd: str, *args: str, **kwargs) -> subprocess.CompletedProcess:
    return run_subprocess("make", *[cmd, *args], **kwargs)

def progress(msg: str="", **kwargs) -> None:
    print(msg, **{"file": sys.stderr, "flush": True, **kwargs})

def dump_smt_for_version(version, program):
  program_basename = pathlib.Path(program).stem
  prover_log_path = f"{version}/{program_basename}.smt2"
  progress(f"Writing SMT log from {program} to {prover_log_path}...")
  run_subprocess(f"./{version}/dafny/dafny", "/compile:0", f"/proverLog:{prover_log_path}", program, check = False)

def get_and_build_dafny(version):
  git("clone", "https://github.com/dafny-lang/dafny.git", version)
  os.chdir(version)
  git("checkout", version)
  make("z3-mac")
  make("exe")
  os.chdir("..")

def get_dafny_release(version):
  if os.path.isdir(version):
    return
  os.mkdir(version)
  os.chdir(version)
  run_subprocess("wget", f"https://github.com/dafny-lang/dafny/releases/download/v{version}/dafny-{version}-x64-osx-10.14.2.zip")
  run_subprocess("unzip", f"dafny-{version}-x64-osx-10.14.2.zip")
  os.chdir("..")

def parse_arguments() -> argparse.Namespace:
  parser = argparse.ArgumentParser(description="Dafny release helper")
  parser.add_argument("version", nargs='*', help="Dafny version (can be provided multiple times)")
  parser.add_argument("--program", help="Target Dafny program")
  return parser.parse_args()

def main() -> None:
  args = parse_arguments()
  
  for version in args.version:
    get_dafny_release(version)
    # get_and_build_dafny(version)
    dump_smt_for_version(version, args.program)

if __name__ == "__main__":
    main()