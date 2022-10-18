import argparse
import subprocess
import sys

def run_subprocess(cmd: str, *args: str, **kwargs) -> subprocess.CompletedProcess:
    print([cmd, *args])
    return subprocess.run([cmd, *args], # pylint: disable=subprocess-run-check
        **{"capture_output": True, "check": False, "encoding": "utf-8", **kwargs})

def git(cmd: str, *args: str, **kwargs) -> subprocess.CompletedProcess:
    return run_subprocess("git", *[cmd, *args], **kwargs)

def dotnet(cmd: str, *args: str, **kwargs) -> subprocess.CompletedProcess:
    return run_subprocess("dotnet", *[cmd, *args], **kwargs)

def dafny(cmd: str, *args: str, **kwargs) -> subprocess.CompletedProcess:
    return run_subprocess("Scripts/dafny", *[cmd, *args], **kwargs)

def progress(msg: str="", **kwargs) -> None:
    print(msg, **{"file": sys.stderr, "flush": True, **kwargs})

def dump_smt_for_version(version, program, prover_log_path):
  progress(f"Checking out {version}...")
  git("checkout", version)
  progress(f"Building Dafny...")
  dotnet("build", "Source/Dafny.sln")
  progress(f"Writing SMT log from {program} to {prover_log_path}...")
  dafny("/compile:0", "/proverLog:" + prover_log_path, program)

def parse_arguments() -> argparse.Namespace:
  parser = argparse.ArgumentParser(description="Dafny release helper")
  parser.add_argument("before", help="First sha")
  parser.add_argument("after", help="Second sha")
  parser.add_argument("program", help="Target Dafny program")
  return parser.parse_args()

def main() -> None:
  args = parse_arguments()
  
  # dump_smt_for_version(args.before, args.program, "./before.smt2")
  dump_smt_for_version(args.after, args.program, "./after.smt2")



if __name__ == "__main__":
    main()