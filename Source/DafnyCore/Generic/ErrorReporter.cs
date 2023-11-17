using System;
using System.Diagnostics.Contracts;

namespace Microsoft.Dafny;

public abstract class ErrorReporter {
  public DafnyOptions Options { get; }

  protected ErrorReporter(DafnyOptions options) {
    this.Options = options;
  }

  public bool ErrorsOnly { get; set; }

  public bool HasErrors => ErrorCount > 0;
  public int ErrorCount => Count(ErrorLevel.Error);
  public bool HasErrorsUntilResolver => ErrorCountUntilResolver > 0;
  public int ErrorCountUntilResolver => CountExceptVerifierAndCompiler(ErrorLevel.Error);

  public virtual bool Message(MessageSource source, ErrorLevel level, string errorId, IToken tok, string msg) {
    if (Options.WarningsAsErrors && level == ErrorLevel.Warning) {
      level = ErrorLevel.Error;
    }

    return MessageCore(source, level, errorId, tok, msg);

  }

  protected abstract bool MessageCore(MessageSource source, ErrorLevel level, string errorId, IToken tok, string msg);

  public void Error(MessageSource source, IToken tok, string msg) {
    Error(source, ParseErrors.ErrorId.none, tok, msg);
  }
  public virtual void Error(MessageSource source, string errorId, IToken tok, string msg) {
    Contract.Requires(tok != null);
    Contract.Requires(msg != null);
    Message(source, ErrorLevel.Error, errorId, tok, msg);
  }

  public abstract int Count(ErrorLevel level);
  public abstract int CountExceptVerifierAndCompiler(ErrorLevel level);

  // This method required by the Parser
  internal void Error(MessageSource source, Enum errorId, Uri uri, int line, int col, string msg) {
    var tok = new Token(line, col);
    tok.Uri = uri;
    Error(source, errorId, tok, msg);
  }

  public void Error(MessageSource source, IToken tok, string format, params object[] args) {
    Contract.Requires(tok != null);
    Contract.Requires(format != null);
    Contract.Requires(args != null);
    Error(source, ParseErrors.ErrorId.none, tok, format, args);
  }

  public void Error(MessageSource source, Enum errorId, IToken tok, string format, params object[] args) {
    Contract.Requires(tok != null);
    Contract.Requires(format != null);
    Contract.Requires(args != null);
    Error(source, errorId.ToString(), tok, String.Format(format, args));
  }

  public void Error(MessageSource source, Enum errorId, IToken tok, string msg) {
    Contract.Requires(tok != null);
    Contract.Requires(msg != null);
    Error(source, errorId.ToString(), tok, msg);
  }

  public void Error(MessageSource source, Declaration d, string format, params object[] args) {
    Contract.Requires(d != null);
    Contract.Requires(format != null);
    Contract.Requires(args != null);
    Error(source, ParseErrors.ErrorId.none, d.tok, format, args);
  }

  public void Error(MessageSource source, Enum errorId, Declaration d, string msg, params object[] args) {
    Contract.Requires(d != null);
    Contract.Requires(msg != null);
    Contract.Requires(args != null);
    Error(source, errorId, d.tok, msg, args);
  }

  public void Error(MessageSource source, Enum errorId, Statement s, string format, params object[] args) {
    Contract.Requires(s != null);
    Contract.Requires(format != null);
    Contract.Requires(args != null);
    Error(source, errorId, s.Tok, format, args);
  }

  public void Error(MessageSource source, Statement s, string format, params object[] args) {
    Contract.Requires(s != null);
    Contract.Requires(format != null);
    Contract.Requires(args != null);
    Error(source, ParseErrors.ErrorId.none, s.Tok, format, args);
  }

  public void Error(MessageSource source, INode v, string format, params object[] args) {
    Contract.Requires(v != null);
    Contract.Requires(format != null);
    Contract.Requires(args != null);
    Error(source, ParseErrors.ErrorId.none, v.Tok, format, args);
  }

  public void Error(MessageSource source, Enum errorId, INode v, string format, params object[] args) {
    Contract.Requires(v != null);
    Contract.Requires(format != null);
    Contract.Requires(args != null);
    Error(source, errorId, v.Tok, format, args);
  }

  public void Error(MessageSource source, Enum errorId, Expression e, string format, params object[] args) {
    Contract.Requires(e != null);
    Contract.Requires(format != null);
    Contract.Requires(args != null);
    Error(source, errorId, e.tok, format, args);
  }

  public void Error(MessageSource source, Expression e, string format, params object[] args) {
    Contract.Requires(e != null);
    Contract.Requires(format != null);
    Contract.Requires(args != null);
    Error(source, ParseErrors.ErrorId.none, e.tok, format, args);
  }

  public void Warning(MessageSource source, Enum errorId, IToken tok, string format, params object[] args) {
    Contract.Requires(tok != null);
    Contract.Requires(format != null);
    Contract.Requires(args != null);
    Warning(source, errorId, tok, String.Format(format, args));
  }

  public void Warning(MessageSource source, Enum errorId, IToken tok, string msg) {
    Contract.Requires(tok != null);
    Contract.Requires(msg != null);
    if (Options.WarningsAsErrors) {
      Error(source, errorId.ToString(), tok, msg);
    } else {
      Message(source, ErrorLevel.Warning, errorId.ToString(), tok, msg);
    }
  }

  public void Warning(MessageSource source, string errorId, IToken tok, string msg) {
    Contract.Requires(tok != null);
    Contract.Requires(msg != null);
    Message(source, ErrorLevel.Warning, errorId, tok, msg);
  }

  public void Deprecated(MessageSource source, Enum errorId, IToken tok, string msg) {
    Contract.Requires(tok != null);
    Contract.Requires(msg != null);
    if (Options.DeprecationNoise != 0) {
      Warning(source, errorId, tok, msg);
    }
  }

  public void Deprecated(MessageSource source, Enum errorId, IToken tok, string format, params object[] args) {
    Contract.Requires(tok != null);
    Contract.Requires(format != null);
    Contract.Requires(args != null);
    if (Options.DeprecationNoise != 0) {
      Warning(source, errorId, tok, String.Format(format, args));
    }
  }

  public void Info(MessageSource source, IToken tok, string msg, object errorId = null) {
    Contract.Requires(tok != null);
    Contract.Requires(msg != null);
    Message(source, ErrorLevel.Info, errorId?.ToString(), tok, msg);
  }

  public void Info(MessageSource source, IToken tok, string msg, params object[] args) {
    Contract.Requires(tok != null);
    Contract.Requires(msg != null);
    Contract.Requires(args != null);
    Info(source, tok, String.Format(msg, args));
  }

  public string ErrorToString(ErrorLevel header, IToken tok, string msg) {
    return $"{tok.TokenToString(Options)}: {header.ToString()}: {msg}";
  }
}