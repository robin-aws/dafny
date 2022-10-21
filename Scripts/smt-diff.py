import argparse
from genericpath import isfile
import subprocess
import sys
import os
import json
import shutil
from pathlib import Path

def run_subprocess(cmd: str, *args: str, check = True, **kwargs) -> subprocess.CompletedProcess:
    print([cmd, *args])
    result = subprocess.run([cmd, *args], # pylint: disable=subprocess-run-check
        **{"capture_output": True, "check": False, "encoding": "utf-8", **kwargs})
    if check and result.returncode != 0:
      raise Exception(result.stdout + result.stderr)
    return result

def git(cmd: str, *args: str, **kwargs) -> subprocess.CompletedProcess:
    return run_subprocess("git", *[cmd, *args], **kwargs)

def dotnet(cmd: str, *args: str, **kwargs) -> subprocess.CompletedProcess:
    return run_subprocess("dotnet", *[cmd, *args], **kwargs)

def dafny(dir: Path, *args: str, **kwargs) -> subprocess.CompletedProcess:
    cmd = dir / "Scripts" / "dafny"
    if not os.path.isfile(cmd):
      cmd = dir / "dafny"
    return run_subprocess(cmd, *args, **kwargs)

def make(cmd: str, *args: str, **kwargs) -> subprocess.CompletedProcess:
    return run_subprocess("make", *[cmd, *args], **kwargs)

def progress(msg: str="", **kwargs) -> None:
    print(msg, **{"file": sys.stderr, "flush": True, **kwargs})

def smt_dir_path(version, program):
  version_dir = f"smt/{version}"
  program_basename = Path(program).stem
  return f"{version_dir}/{program_basename}"
  
def dump_smt_for_version(version, dafny_dir, program):
  prover_log_path = smt_dir_path(version, program)
  if os.path.isdir(prover_log_path):
    if version.startswith("local"):
      # Don't maintain old state
      progress(f"Deleting smt files for 'local': {prover_log_path}")
      shutil.rmtree(prover_log_path)
    else:
      progress(f"{prover_log_path} already exists, reusing")
      return prover_log_path

  os.makedirs(prover_log_path)
  
  progress(f"Writing SMT log from {program} to {prover_log_path}...")
  dafny(dafny_dir, 
         "/compile:0", 
         f"/proverLog:{prover_log_path}/@FILE@_@PROC@.smt2",
         "/proverOpt:SOLVER=noop",
         program,
         check = False)
  return prover_log_path

def get_and_build_dafny(version):
  if version == "local":
    version_dir = Path(".")
    old_dir = os.getcwd()
    os.chdir(version_dir)

    # Remove generated code locations, which have changed over time
    Path(version_dir / "Source" / "Dafny" / "Scanner.cs").unlink(missing_ok=True)
    Path(version_dir / "Source" / "Dafny" / "Parser.cs").unlink(missing_ok=True)
    Path(version_dir / "Source" / "DafnyCore" / "Scanner.cs").unlink(missing_ok=True)
    Path(version_dir / "Source" / "DafnyCore" / "Parser.cs").unlink(missing_ok=True)
  else:
    root = Path("dafny_sources")
    version_dir = root / version
    if version_dir.exists():
      return version_dir

    version_dir.mkdir(parents=True, exist_ok=True)

    git("clone", "https://github.com/dafny-lang/dafny.git", version_dir)
    old_dir = os.getcwd()
    os.chdir(version_dir)
    git("checkout", version)
    make("z3-mac")

  make("exe")
  os.chdir(old_dir)
  return version_dir

def get_dafny_release(version):
  os.makedirs(version)
  os.chdir(version)
  run_subprocess("wget", f"https://github.com/dafny-lang/dafny/releases/download/v{version}/dafny-{version}-x64-osx-10.14.2.zip")
  run_subprocess("unzip", f"dafny-{version}-x64-osx-10.14.2.zip")
  os.chdir("..")

def parse_arguments() -> argparse.Namespace:
  parser = argparse.ArgumentParser(description="Dafny release helper")
  parser.add_argument("version", nargs='*', help="Dafny version (can be provided multiple times)")
  parser.add_argument("--program", help="Target Dafny program")
  parser.add_argument("--check", dest='check', action='store_true')
  
  return parser.parse_args()

def compare_versions(versions, dafny_dirs, program):
  previous_version = None
  for version in versions:
    dump_smt_for_version(version, dafny_dirs[version], program)

    if previous_version is not None:
      result = run_subprocess("diff", "-rq", 
        smt_dir_path(previous_version, program),
        smt_dir_path(version, program))
      progress(result.stdout)
    previous_version = version

def main() -> None:
  args = parse_arguments()
  
  version_dirs = {}
  if args.version:
    versions = args.version

    for version in versions:
      version_dirs[version] = get_and_build_dafny(version)
  else:
    root = Path("dafny_releases")
    cache_file = root / "releases.json"
    bs = cache_file.read_bytes()
    js = json.loads(bs.decode("utf-8"))
    versions = reversed([r["tag_name"] for r in js ])
    
    for version in versions:
      version_dirs[version] = root / "binaries" / version

  if args.check:
    for version in versions:
      dafny_dir = version_dirs[version]
      first = dump_smt_for_version(version, dafny_dir, args.program)
      second = dump_smt_for_version(version + "-2", dafny_dir, args.program)
      try:
        run_subprocess("diff", "-rq", first, second)
      except:
        pass
      else:
        raise Exception("No difference!")
  else:
    compare_versions(versions, version_dirs, args.program)

if __name__ == "__main__":
    main()