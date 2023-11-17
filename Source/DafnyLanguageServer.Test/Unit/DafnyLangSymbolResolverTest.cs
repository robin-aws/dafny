﻿using System;
using System.Collections.Generic;
using Microsoft.Dafny.LanguageServer.Language;
using Microsoft.Dafny.LanguageServer.Language.Symbols;
using Microsoft.Dafny.LanguageServer.Workspace;
using Microsoft.Extensions.Logging;
using Moq;

namespace Microsoft.Dafny.LanguageServer.IntegrationTest.Unit;

public class DafnyLangSymbolResolverTest {
  private DafnyLangSymbolResolver dafnyLangSymbolResolver;

  public DafnyLangSymbolResolverTest() {
    var loggerFactory = new Mock<ILoggerFactory>();
    dafnyLangSymbolResolver = new DafnyLangSymbolResolver(
      new Mock<ILogger<DafnyLangSymbolResolver>>().Object,
      new Mock<ILogger<CachingResolver>>().Object,
      new Mock<ITelemetryPublisher>().Object
    );
  }

  class CollectingErrorReporter : BatchErrorReporter {
    public Dictionary<ErrorLevel, List<DafnyDiagnostic>> GetErrors() {
      return this.AllMessagesByLevel;
    }

    public CollectingErrorReporter(DafnyOptions options) : base(options) {
    }
  }

  class DummyModuleDecl : LiteralModuleDecl {
    public DummyModuleDecl() : base(
      new DefaultModuleDefinition(), null, Guid.NewGuid()) {
    }
    public override object Dereference() {
      return this;
    }
  }
}
