﻿using Microsoft.Dafny.LanguageServer.Language;
using Microsoft.Dafny.LanguageServer.Language.Symbols;
using Microsoft.Dafny.LanguageServer.Workspace;
using Moq;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using System;
using System.Collections.Immutable;
using System.IO;
using System.Threading;
using System.Threading.Tasks;
using DafnyCore.Test;
using Microsoft.Boogie;
using Microsoft.Extensions.Logging;
using OmniSharp.Extensions.LanguageServer.Protocol;
using Xunit;
using Xunit.Abstractions;

namespace Microsoft.Dafny.LanguageServer.IntegrationTest.Unit {
  public class TextDocumentLoaderTest {
    private readonly TextWriter output;

    private Mock<IFileSystem> fileSystem;
    private Mock<IDafnyParser> parser;
    private Mock<ISymbolResolver> symbolResolver;
    private Mock<ISymbolTableFactory> symbolTableFactory;
    private Mock<IGhostStateDiagnosticCollector> ghostStateDiagnosticCollector;
    private TextDocumentLoader textDocumentLoader;
    private Mock<ILogger<ITextDocumentLoader>> logger;

    public TextDocumentLoaderTest(ITestOutputHelper output) {
      this.output = new WriterFromOutputHelper(output);
      parser = new();
      symbolResolver = new();
      symbolTableFactory = new();
      ghostStateDiagnosticCollector = new();
      fileSystem = new();
      logger = new Mock<ILogger<ITextDocumentLoader>>();
      textDocumentLoader = TextDocumentLoader.Create(
        parser.Object,
        symbolResolver.Object,
        symbolTableFactory.Object,
        ghostStateDiagnosticCollector.Object,
        logger.Object
      );
    }

    private static VersionedTextDocumentIdentifier CreateTestDocumentId() {
      return new VersionedTextDocumentIdentifier() {
        Uri = DocumentUri.Parse("untitled:untitled1"),
        Version = 1,
      };
    }

    private static DocumentTextBuffer CreateTestDocument() {
      return new DocumentTextBuffer(new TextDocumentItem() {
        Uri = DocumentUri.Parse("untitled:untitled1"),
        LanguageId = "dafny",
        Version = 1,
        Text = ""
      });
    }

    [Fact]
    public async Task LoadReturnsCanceledTaskIfOperationIsCanceled() {
      var source = new CancellationTokenSource();
      parser.Setup(p => p.Parse(
          It.IsAny<Compilation>(),
          It.IsAny<CancellationToken>())).Callback(() => source.Cancel())
        .Throws<TaskCanceledException>();
      var task = textDocumentLoader.ParseAsync(GetCompilation(), source.Token);
      try {
        await task;
        Assert.Fail("document load was not cancelled");
      } catch (Exception e) {
        Assert.IsType<TaskCanceledException>(e);
        Assert.True(task.IsCanceled);
        Assert.False(task.IsFaulted);
      }
    }

    private Compilation GetCompilation() {
      var versionedTextDocumentIdentifier = CreateTestDocumentId();
      var uri = versionedTextDocumentIdentifier.Uri.ToUri();
      var fs = new InMemoryFileSystem(ImmutableDictionary<Uri, string>.Empty.Add(uri, ""));
      var file = DafnyFile.CreateAndValidate(new ErrorReporterSink(DafnyOptions.Default), fs, DafnyOptions.Default, uri, Token.NoToken);
      var input = new CompilationInput(DafnyOptions.Default, 0,
        ProjectManagerDatabase.ImplicitProject(uri));
      var engine = new ExecutionEngine(DafnyOptions.Default, new VerificationResultCache(),
        CustomStackSizePoolTaskScheduler.Create(0, 0));
      var compilation = new Compilation(new Mock<ILogger<Compilation>>().Object, new Mock<IFileSystem>().Object, textDocumentLoader,
        new Mock<IProgramVerifier>().Object, engine, input);
      compilation.RootFiles = new[] { file };
      return compilation;
    }

    [Fact]
    public async Task LoadReturnsFaultedTaskIfAnyExceptionOccured() {
      parser.Setup(p => p.Parse(It.IsAny<Compilation>(),
          It.IsAny<CancellationToken>()))
        .Throws<InvalidOperationException>();
      var task = textDocumentLoader.ParseAsync(GetCompilation(), default);
      try {
        await task;
        Assert.Fail("document load did not fail");
      } catch (Exception e) {
        Assert.IsType<InvalidOperationException>(e);
        Assert.False(task.IsCanceled);
        Assert.True(task.IsFaulted);
      }
    }
  }
}
