import {
    //createConnection,
    //TextDocuments,
    TextDocument,
    Diagnostic,
    DiagnosticSeverity,
    //ProposedFeatures,
    InitializeParams,
    DidChangeConfigurationNotification,
    CompletionItem,
    CompletionItemKind,
    TextDocumentPositionParams
  } from  'vscode-languageserver-protocol';

  // Create a connection for the server. The connection uses Node's IPC as a transport.
// Also include all preview / proposed LSP features.
//let connection = createConnection(ProposedFeatures.all);

// Create a simple text document manager. The text document manager
// supports full document sync only
//let documents: TextDocuments = new TextDocuments();

