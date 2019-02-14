'use strict';

const vscode = require("vscode");
const vscc = require("vscode-languageclient");

function activate (context) {
    vscode.window.showInformationMessage('Going to activate!');
    let clientOptions = {
        documentSelector: [
            {scheme: 'file', language: 'lp'}
        ]
    };

    let client = null;

    const restart = () => {
        if (client) {
            client.stop();
        }
        vscode.window.showInformationMessage('Going to start!');
        client = new vscc.LanguageClient(
            'lp-lsp-server',
            'LP Language Server',
            {
                command: 'lp-lsp',
                args: [ '--std' ]
            },
            clientOptions
        );
        context.subscriptions.push(client.start());
    };

    vscode.commands.registerCommand('vscode-lp.restart', restart);

    restart();
}

exports.activate = activate;
