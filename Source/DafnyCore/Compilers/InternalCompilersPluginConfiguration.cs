using Microsoft.Dafny.Plugins;

namespace Microsoft.Dafny.Compilers;

internal class InternalCompilersPluginConfiguration : Plugins.PluginConfiguration {
  public static readonly InternalCompilersPluginConfiguration Singleton = new();

  public override IExecutableBackend[] GetCompilers(DafnyOptions options) {
    return new IExecutableBackend[] {
      new CsharpBackend(options),
      new JavaScriptBackend(options),
      new GoBackend(options),
      new JavaBackend(options),
      new PythonBackend(options),
      new CppCompilerBackend(options),
      new LibraryBackend(options),
      new RustBackend(options),
      new ResolvedDesugaredExecutableDafnyBackend(options)
    };
  }
}