/* --------------------------------------------------------------------------------------------
 * Copyright (c) Microsoft Corporation. All rights reserved.
 * Licensed under the MIT License. See License.txt in the project root for license information.
 * ------------------------------------------------------------------------------------------ */

import * as path from 'path';
import * as fs from 'fs';
import * as net from 'net';
import * as child_process from 'child_process';
import { workspace, ExtensionContext, Position, Uri, commands, window, WebviewPanel, ViewColumn, TextEditor, TextDocument } from 'vscode';


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

	//create the server /Users/houdamouzoun/.opam/4.05.0/bin/lp-lsp

	let serverOptions = {
		command: '/lp-lsp',
		args: [ '--std' ]
	};

	// Options to control the language client
	let clientOptions: LanguageClientOptions = {
		// Register the server for lp documents
		documentSelector: [{ scheme: 'file', language: 'lp' }],
		synchronize: {
			// Notify the server about file changes to '.clientrc files contained in the workspace
			fileEvents: workspace.createFileSystemWatcher('**/.clientrc')
		}
	};

	// Create the language client and start the client.
	client = new LanguageClient(
		'languageServerExample',
		'Language Server Example',
		serverOptions,
		clientOptions
	);
	
	// Start the client. This will also launch the server
	client.start();

	//display goals
	//onselectionchange sendgoalsrequest

	client.onReady().then(() => {

		  // Create and show panel
			
			const panel = window.createWebviewPanel(
				'goals',
				'Goals',
				ViewColumn.Two,
				{}
			);
			
			workspace.onDidOpenTextDocument(e => {
				if(e.languageId == 'lp'){
					window.showTextDocument(e, ViewColumn.One, true);
					restart(panel)
				}
			})
			
				
		window.onDidChangeActiveTextEditor(e =>
			restart(panel)
		);
			
	context.subscriptions.push(
		commands.registerCommand('getGoals.start', () => {
			
		})

	);


	});

}
	

	function restart(panel : WebviewPanel){
		
			const editor = window.activeTextEditor;
			
			const doc = editor == undefined? null : editor.document; 
			const selec = editor == undefined? null : editor.selection;
			const uri = doc == null? null : doc.uri;
		
			// And set its HTML content
			panel.webview.html = getWebviewContent("");
			window.showInformationMessage('Going to start!');
			window.onDidChangeTextEditorSelection(e => {
				let selec = e.textEditor.selection;
				if (uri != null){
					sendGoalsRequest(selec.active, panel, uri)
				} 
			}
				);
	}
	
	function getWebviewContent(goals : String) {
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
		htmlPage2 =	` </p>
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
		let goalsState : String;
		let doc = {uri : uri.toString()}
		let cursor = {textDocument : doc, position : position}; 
		const req = new RequestType<ParamsGoals, GoalResp, void, void>("proof/goals");
		client.sendRequest(req, cursor).then((goals) => {
		let a = goals.contents;
		//return goals;
		panel.webview.html = getWebviewContent(a);
		}); 
	}

export function deactivate(): Thenable<void> | undefined {
	if (!client) {
		return undefined;
	}
	return client.stop();
}
