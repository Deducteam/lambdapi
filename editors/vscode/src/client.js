"use strict";
/* --------------------------------------------------------------------------------------------
 * Copyright (c) Microsoft Corporation. All rights reserved.
 * Licensed under the MIT License. See License.txt in the project root for license information.
 * ------------------------------------------------------------------------------------------ */
exports.__esModule = true;
var path = require("path");
var vscode_1 = require("vscode");
var vscode_languageclient_1 = require("vscode-languageclient");
var client;
function activate(context) {
    // The server is implemented in node
    var serverModule = context.asAbsolutePath(path.join('..', '..', '..', 'lp-lsp', 'lp_lsp.ml')
    //path.join('server', 'out', 'server.js')
    );
    // The debug options for the server
    // --inspect=6009: runs the server in Node's Inspector mode so VS Code can attach to the server for debugging
    var debugOptions = { execArgv: ['--nolazy', '--inspect=6009'] };
    // If the extension is launched in debug mode then the debug server options are used
    // Otherwise the run options are used
    var serverOptions = {
        run: { module: serverModule, transport: vscode_languageclient_1.TransportKind.ipc },
        debug: {
            module: serverModule,
            transport: vscode_languageclient_1.TransportKind.ipc,
            options: debugOptions
        }
    };
    // Options to control the language client
    var clientOptions = {
        // Register the server for plain text documents
        documentSelector: [{ scheme: 'file', language: 'lp' }],
        synchronize: {
            // Notify the server about file changes to '.clientrc files contained in the workspace
            fileEvents: vscode_1.workspace.createFileSystemWatcher('**/.clientrc')
        }
    };
    // Create the language client and start the client.
    client = new vscode_languageclient_1.LanguageClient('languageServerExample', 'Language Server Example', serverOptions, clientOptions);
    // Start the client. This will also launch the server
    client.start();
    //display goals
    //onselectionchange sendgoalsrequest
    client.onReady().then(function () {
        context.subscriptions.push(vscode_1.commands.registerCommand('getGoals.start', function () {
            vscode_1.workspace.onDidOpenTextDocument(function (_) {
                var editor = vscode_1.window.activeTextEditor;
                var doc = editor == undefined ? null : editor.document;
                var uri = doc == null ? null : doc.uri;
                if (doc != null) {
                    vscode_1.window.showTextDocument(doc, vscode_1.ViewColumn.One);
                }
                var notifOpen = new vscode_languageclient_1.NotificationType("textDocument/didOpen");
                client.sendNotification(notifOpen, uri);
                var notifChange = new vscode_languageclient_1.NotificationType("textDocument/didChange");
                client.sendNotification(notifChange, uri);
                // Create and show panel
                var panel = vscode_1.window.createWebviewPanel('goals', 'Goals', vscode_1.ViewColumn.Two, {});
                // And set its HTML content
                panel.webview.html = getWebviewContent(null);
                vscode_1.window.onDidChangeTextEditorSelection(function (e) {
                    return sendGoalsRequest(editor.selection.active, panel, uri);
                });
                var notifClose = new vscode_languageclient_1.NotificationType("textDocument/didClose");
                client.sendNotification(notifClose, uri);
            });
        }));
    });
}
exports.activate = activate;
function getWebviewContent(goals) {
    var goalsPrint;
    var htmlPage1;
    var htmlPage2;
    goalsPrint = goals == null ? "" : goals.toString();
    htmlPage1 = "<!DOCTYPE html>\n\t\t<html lang=\"en\">\n\t\t<head>\n\t\t\t<meta charset=\"UTF-8\">\n\t\t\t<meta name=\"viewport\" content=\"width=device-width, initial-scale=1.0\">\n\t\t\t<title> Goals</title>\n\t\t</head>\n\t\t<body>\n\t\t\t<p><pre> ";
    htmlPage2 = " </pre></p>\n\t\t</body>\n\t\t</html>";
    return htmlPage1.concat(goalsPrint.concat(htmlPage2));
}
function sendGoalsRequest(position, panel, uri) {
    var goalsState;
    var cursor = { uri: uri, line: position.line, character: position.character };
    //---client.onRequest(new RequestType("../../../../../lp-lsp/lp-lsp/getGoals", caret, string))
    var req = new vscode_languageclient_1.RequestType("proof/goals");
    client.sendRequest(req, cursor).then(function (goals) {
        //return goals
        return goals;
        //panel.webview.html = getWebviewContent(goals);
    });
}
function deactivate() {
    if (!client) {
        return undefined;
    }
    return client.stop();
}
exports.deactivate = deactivate;
