/* --------------------------------------------------------------------------------------------
 * Copyright (c) Microsoft Corporation. All rights reserved.
 * Licensed under the MIT License. See License.txt in the project root for license information.
 * ------------------------------------------------------------------------------------------ */

import { workspace, ExtensionContext, Position, Uri, commands, window, WebviewPanel, ViewColumn, TextEditor, TextDocument } from 'vscode';

// Insiders API, disabled
// import { WebviewEditorInset } from 'vscode';

import {
    LanguageClient,
    LanguageClientOptions,
    ServerOptions,
    TransportKind,
    RequestType,
    NotificationType,
    TextDocumentIdentifier,
    RegistrationRequest,
} from 'vscode-languageclient';

let client: LanguageClient;

export function activate(context: ExtensionContext) {

    let serverOptions = {
        command: 'lp-lsp',    // XXX: Get from configuration
        args: [ '--std' ]
    };

    let clientOptions: LanguageClientOptions = {
        documentSelector: [{ scheme: 'file', language: 'lp' }],
    };

    const restart = () => {

        if (client) {
            client.stop();
        }

        client = new LanguageClient(
            'LambdaPi-VSCode',
            'Lambdapi Language Server',
            serverOptions,
            clientOptions
        );

        client.onReady().then(() => {

            // Create and show panel
            const panel = window.createWebviewPanel(
                'goals',
                'Goals',
                ViewColumn.Two,
                {}
            );

            window.onDidChangeActiveTextEditor(e => refresh(panel, e));
            window.onDidChangeTextEditorSelection(e => refresh(panel, e.textEditor));

        });
        context.subscriptions.push(client.start());
    };

    commands.registerCommand('extension.vscode-lp.restart', restart);

    restart();
}

function refresh(panel : WebviewPanel, editor : TextEditor | undefined) {

    if(editor)
        sendGoalsRequest(editor.selection.active, panel, editor.document.uri);

}

function buildGoalsContent(goals : String) {
    let goalsPrint : String;
    let htmlPage1 : String;
    let htmlPage2 : String;
    goalsPrint = goals;
    htmlPage1 =  `<!DOCTYPE html>
<html lang="en">
<head>
<meta charset="UTF-8">
<meta name="viewport" content="width=device-width, initial-scale=1.0">
<title> Goals</title>
</head>
<body>
<p> `;
    let date = new Date();
    let datestring = date.toLocaleDateString(undefined, {
        hour : '2-digit',
        minute : '2-digit',
        second : '2-digit'
    });
    htmlPage2 =     ` </p>
</body>
</html>`;
    let datestring1 = '';

    return htmlPage1+ datestring1+goalsPrint+htmlPage2;
}

export interface TextDocumentIdent{
    uri : String
}

export interface ParamsGoals {
    textDocument : TextDocumentIdent
    position : Position
}

export interface GoalResp {
    contents : String
}

function sendGoalsRequest(position: Position, panel : WebviewPanel, uri : Uri) {

    let doc = {uri : uri.toString()}
    let cursor = {textDocument : doc, position : position};
    const req = new RequestType<ParamsGoals, GoalResp, void, void>("proof/goals");
    client.sendRequest(req, cursor).then((goals) => {
        panel.webview.html = buildGoalsContent(goals.contents);
        // Disabled as this is experimental
	// let wb = window.createWebviewTextEditorInset(window.activeTextEditor, line, height);
	// wb.webview.html = panel.webview.html;
    }, () => { panel.webview.html = buildGoalsContent(""); });
}

export function deactivate(): Thenable<void> | undefined {
    if (!client) {
        return undefined;
    }
    return client.stop();
}
