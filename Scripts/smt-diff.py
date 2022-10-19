import argparse
from genericpath import isfile
import subprocess
import sys
import os
import json
from pathlib import Path

def run_subprocess(cmd: str, *args: str, check = True, **kwargs) -> subprocess.CompletedProcess:
    print([cmd, *args])
    result = subprocess.run([cmd, *args], # pylint: disable=subprocess-run-check
        **{"capture_output": True, "check": False, "encoding": "utf-8", **kwargs})
    if check and result.returncode != 0:
      raise Exception(result.stderr)
    return result

def git(cmd: str, *args: str, **kwargs) -> subprocess.CompletedProcess:
    return run_subprocess("git", *[cmd, *args], **kwargs)

def dotnet(cmd: str, *args: str, **kwargs) -> subprocess.CompletedProcess:
    return run_subprocess("dotnet", *[cmd, *args], **kwargs)

def dafny(dir: str, *args: str, **kwargs) -> subprocess.CompletedProcess:
    # Attempting to make this work for Macs...
    # main_dll = f"{dir}/Dafny.dll"
    # if not os.path.isfile(main_dll):
    #   main_dll = f"{dir}/DafnyPipeline.dll"
    # return dotnet(main_dll, *args, **kwargs)
    return dotnet(f"{dir}/dafny", *args, **kwargs)

def make(cmd: str, *args: str, **kwargs) -> subprocess.CompletedProcess:
    return run_subprocess("make", *[cmd, *args], **kwargs)

def progress(msg: str="", **kwargs) -> None:
    print(msg, **{"file": sys.stderr, "flush": True, **kwargs})

def smt_file_path(version, program):
  version_dir = f"dafny_releases/smt/{version}"
  if not os.path.isdir(version_dir):
    os.makedirs(version_dir)

  program_basename = Path(program).stem
  return f"{version_dir}/{program_basename}.smt2"
  
def dump_smt_for_version(version, program):
  prover_log_path = smt_file_path(version, program)
  if os.path.isfile(prover_log_path):
    progress(f"{prover_log_path} already exists, reusing")
    return

  progress(f"Writing SMT log from {program} to {prover_log_path}...")
  dafny(f"dafny_releases/binaries/{version}", 
         "/compile:0", 
         f"/proverLog:{prover_log_path}",
         "/proverOpt:SOLVER=noop",
         program)

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

def compare_versions(versions, program):
  previous_version = None
  for version in versions:
    dump_smt_for_version(version, program)

    if previous_version is not None:
      result = run_subprocess("diff", "-q", 
        smt_file_path(previous_version, program),
        smt_file_path(version, program),
        check = False)
      progress(result.stdout)
    previous_version = version

def main() -> None:
  args = parse_arguments()
  
  versions = None
  if args.version:
    versions = args.version
  else:
    cache_file = Path("dafny_releases/releases.json")
    bs = cache_file.read_bytes()
    js = json.loads(bs.decode("utf-8"))
    versions = reversed([r["tag_name"] for r in js ])

  compare_versions(versions, args.program)

if __name__ == "__main__":
    main()