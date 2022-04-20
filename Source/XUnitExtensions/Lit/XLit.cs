using System.Diagnostics;
using System.IO;
using CommandLine;

namespace XUnitExtensions.Lit; 

public class XLit {
  public class Options {

    [Value(0)]
    public string? File { get; set; } = default!;
  }

  public static int Main(string[] args) {
    Parser.Default.ParseArguments<Options>(args).WithParsed(o => {

    });
    return 0;
  }

  public static int RunTest(FileInfo solutionOrProjectFile, FileInfo testFile) {
    var psi = new ProcessStartInfo("dotnet", "") {
      CreateNoWindow = true,
      UseShellExecute = false,
      RedirectStandardInput = false,
      RedirectStandardOutput = false,
      RedirectStandardError = false,
    };
    psi.ArgumentList.Add("test");
    psi.ArgumentList.Add(solutionOrProjectFile.FullName);
    psi.ArgumentList.Add("--filter");
    // TODO: Need to be more precise for this to work well
    psi.ArgumentList.Add($"DisplayName~{testFile.Name}");

    var dotnetTestProcess = new Process { StartInfo = psi };
    dotnetTestProcess.Start();
    dotnetTestProcess.WaitForExit();
    return dotnetTestProcess.ExitCode;
  }

  private static FileInfo FindSolutionFile(string fromPath) {
    var dir = new DirectoryInfo(fromPath);
    while (dir != null) {
      foreach (var file in dir.GetFiles()) {
        var extension = file.Extension;
        if (extension is "csproj" or "sln") {
          // TODO: Check for duplicates
          return file;
        }
      }

      dir = dir.Parent;
    }

    return null;
  }
}