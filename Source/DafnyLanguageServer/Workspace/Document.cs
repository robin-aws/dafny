﻿using System;
using OmniSharp.Extensions.LanguageServer.Protocol;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using System.Collections.Generic;
using System.Linq;
using Microsoft.Boogie;
using Microsoft.Dafny.LanguageServer.Language;
using Microsoft.Dafny.LanguageServer.Language.Symbols;
using Microsoft.Dafny.LanguageServer.Workspace.Notifications;
using Microsoft.Extensions.DependencyInjection;
using Microsoft.Extensions.Logging;
using Range = OmniSharp.Extensions.LanguageServer.Protocol.Models.Range;

namespace Microsoft.Dafny.LanguageServer.Workspace {

  /// <summary>
  /// Internal representation of a specific version of a Dafny document.
  ///
  /// Only one instance should exist of a specific version.
  /// Asynchronous compilation tasks use this instance to synchronise on.
  ///
  /// When verification starts, no new instances of Compilation will be created for this version.
  /// There can be different verification threads that update the state of this object.
  /// </summary>
  public class Document {
    public DocumentTextBuffer TextDocumentItem { get; }
    public DocumentUri Uri => TextDocumentItem.Uri;
    public int Version => TextDocumentItem.Version!.Value;

    public Document(DocumentTextBuffer textDocumentItem) {
      TextDocumentItem = textDocumentItem;
    }

    public virtual IEnumerable<DafnyDiagnostic> Diagnostics => Enumerable.Empty<DafnyDiagnostic>();

    public IdeState InitialIdeState(DafnyOptions options) {
      return ToIdeState(new IdeState(TextDocumentItem, Array.Empty<Diagnostic>(),
        SymbolTable.Empty(), SignatureAndCompletionTable.Empty(options, TextDocumentItem), new Dictionary<ImplementationId, IdeImplementationView>(),
        Array.Empty<Counterexample>(),
        false, Array.Empty<Diagnostic>(),
        GetInitialDocumentVerificationTree()));
    }

    public virtual VerificationTree GetInitialDocumentVerificationTree() {
      return new DocumentVerificationTree(TextDocumentItem);
    }

    /// <summary>
    /// Collects information to present to the IDE
    /// </summary>
    public virtual IdeState ToIdeState(IdeState previousState) {
      return previousState with {
        TextDocumentItem = TextDocumentItem,
        ImplementationsWereUpdated = false,
      };
    }
  }

  public class DocumentAfterParsing : Document {
    private readonly IReadOnlyList<DafnyDiagnostic> parseDiagnostics;

    public DocumentAfterParsing(DocumentTextBuffer textDocumentItem,
      Dafny.Program program,
      IReadOnlyList<DafnyDiagnostic> parseDiagnostics) : base(textDocumentItem) {
      this.parseDiagnostics = parseDiagnostics;
      Program = program;
    }

    public override IEnumerable<DafnyDiagnostic> Diagnostics => parseDiagnostics;

    public Dafny.Program Program { get; }

    public override IdeState ToIdeState(IdeState previousState) {
      return previousState with {
        TextDocumentItem = TextDocumentItem,
        ResolutionDiagnostics = Diagnostics.Select(d => d.ToLspDiagnostic()),
        ImplementationsWereUpdated = false,
      };
    }
  }

  public class DocumentAfterTranslation : DocumentAfterResolution {
    public DocumentAfterTranslation(
      IServiceProvider services,
      DocumentTextBuffer textDocumentItem,
      Dafny.Program program,
      IReadOnlyList<DafnyDiagnostic> parseAndResolutionDiagnostics,
      SymbolTable? symbolTable,
      SignatureAndCompletionTable signatureAndCompletionTable,
      IReadOnlyList<Diagnostic> ghostDiagnostics,
      IReadOnlyList<IImplementationTask> verificationTasks,
      List<Counterexample> counterexamples,
      Dictionary<ImplementationId, ImplementationView> implementationIdToView,
      VerificationTree verificationTree)
      : base(textDocumentItem, program, parseAndResolutionDiagnostics, symbolTable, signatureAndCompletionTable, ghostDiagnostics) {
      VerificationTree = verificationTree;
      VerificationTasks = verificationTasks;
      Counterexamples = counterexamples;
      ImplementationIdToView = implementationIdToView;

      GutterProgressReporter = new VerificationProgressReporter(
        services.GetRequiredService<ILogger<VerificationProgressReporter>>(),
        this,
        services.GetRequiredService<INotificationPublisher>(),
        services.GetRequiredService<DafnyOptions>());
    }

    public override VerificationTree GetInitialDocumentVerificationTree() {
      return VerificationTree;
    }

    public override IdeState ToIdeState(IdeState previousState) {
      IEnumerable<KeyValuePair<ImplementationId, IdeImplementationView>> implementationViewsWithMigratedDiagnostics = ImplementationIdToView.Select(kv => {
        IEnumerable<Diagnostic> diagnostics = kv.Value.Diagnostics.Select(d => d.ToLspDiagnostic());
        if (kv.Value.Status < PublishedVerificationStatus.Error) {
          diagnostics = previousState.ImplementationIdToView.GetValueOrDefault(kv.Key)?.Diagnostics ?? diagnostics;
        }

        var value = new IdeImplementationView(kv.Value.Range, kv.Value.Status, diagnostics.ToList());
        return new KeyValuePair<ImplementationId, IdeImplementationView>(kv.Key, value);
      });
      return base.ToIdeState(previousState) with {
        ImplementationsWereUpdated = true,
        VerificationTree = VerificationTree,
        Counterexamples = new List<Counterexample>(Counterexamples),
        ImplementationIdToView = new Dictionary<ImplementationId, IdeImplementationView>(implementationViewsWithMigratedDiagnostics)
      };
    }

    public override IEnumerable<DafnyDiagnostic> Diagnostics => base.Diagnostics.Concat(
      ImplementationIdToView.SelectMany(kv => kv.Value.Diagnostics) ?? Enumerable.Empty<DafnyDiagnostic>());

    /// <summary>
    /// Contains the real-time status of all verification efforts.
    /// Can be migrated from a previous document
    /// The position and the range are never sent to the client.
    /// </summary>
    public VerificationTree VerificationTree { get; set; }
    public IReadOnlyList<IImplementationTask> VerificationTasks { get; set; }
    public IVerificationProgressReporter GutterProgressReporter { get; set; }
    public List<Counterexample> Counterexamples { get; set; }
    public Dictionary<ImplementationId, ImplementationView> ImplementationIdToView { get; set; }
  }

  public record ImplementationView(Range Range, PublishedVerificationStatus Status, IReadOnlyList<DafnyDiagnostic> Diagnostics);

  public record BufferLine(int LineNumber, int StartIndex, int EndIndex);
}
